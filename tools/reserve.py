#!/usr/bin/env python3
"""One-issue reservation ledger with an authenticated, single-writer broker.

Clients post JSON requests, never edit the ledger. A request is not a lease
until the trusted workflow persists an accepted result and the matching row.
The workflow must be deployed on the default branch before requests can work.

The broker drains comments after its durable cursor, so replaced pending
workflow runs and retries cannot lose or repeat accepted operations. All writers,
including sweep, must use the same workflow concurrency group. Manual ledger
maintenance requires pausing that writer; GitHub issue edits are not a CAS API.

Operational bounds: 64 recent results, 256 rows, 2 KiB requests, and a conservative
60,000-byte UTF-8 issue body. If even a rejection result cannot fit, neither rows
nor cursor change. An expired result or timeout is unconfirmed, not
success. Legacy rows remain ownerless until expiry or maintainer reconciliation.
Unmatchable evidence stays in the request comment unless the deployed trusted
broker archives a proved closed pair to Git before deletion. Clients never
write repository contents, delete comments, or create issues.
"""

import argparse
import base64
import copy
import datetime
import html
import hashlib
import json
import os
import re
import subprocess
import sys
import time


KIT_REPO = os.environ.get("FFTA_KIT_REPO", "shubshub/fftadecomp-kit")
DECOMP_REPO = os.environ.get("FFTA_REPO", "shubshub/fftadecomp")
LEDGER_TITLE = "address ledger"
LEDGER_NUMBER = None
START = "<!-- ffta-ledger:start -->"
END = "<!-- ffta-ledger:end -->"
STATE_START = "<!-- ffta-ledger-state\n"
STATE_END = "\nffta-ledger-state -->"
REQUEST_PREFIX = "<!-- ffta-reservation-request:v1 -->\n"
ARCHIVE_REF = "refs/heads/ledger-receipts-v1"
ARCHIVE_FORMAT = {"version": 1, "purpose": "authenticated-reservation-receipts"}
ARCHIVE_BATCH = 16
STALE_DAYS = 3
MAX_RESULTS = 64
MAX_ROWS = 256
MAX_REQUEST_BYTES = 2048
MAX_BODY_BYTES = 60000
MAX_ISSUE_COMMENTS = 2500
COMMENT_CAPACITY_MESSAGE = "Commenting is disabled on issues with more than 2500 comments"
READ_RETRY_DELAYS = (1, 2)
HERE = os.path.dirname(os.path.abspath(__file__))
UNMATCHABLE_DB = os.path.join(HERE, "..", "known-unmatchable.json")
ROW_FIELDS = {"address", "who", "claimed_at", "last_seen", "note",
              "owner_id", "claim_id"}
RESULT_FIELDS = {"request_id", "owner_id", "who", "operation", "address",
                 "claim_id", "status", "code", "message"}
COMMENTS_QUERY = """query($owner:String!, $name:String!, $issue:Int!, $after:String) {
  repository(owner:$owner, name:$name) {
    issue(number:$issue) {
      comments(first:100, after:$after) {
        edges {
          cursor
          node {
            fullDatabaseId
            body
            author {
              __typename
              ... on User { databaseId }
              ... on Bot { databaseId }
            }
          }
        }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}"""
CLAIM_QUERY = """query($owner:String!, $name:String!, $after:String) {
  repository(owner:$owner, name:$name) {
    defaultBranchRef { name }
    object(expression:"HEAD:src") { __typename ... on Tree { entries { name type } } }
    pullRequests(first:20, states:OPEN, after:$after) {
      nodes {
        number title body state headRefOid
        headRepository { nameWithOwner }
      }
      pageInfo { hasNextPage endCursor }
    }
  }
}"""
PR_HEAD_QUERY = """query($owner:String!, $name:String!, $number:Int!) {
  repository(owner:$owner, name:$name) {
    pullRequest(number:$number) {
      number state headRefOid
      headRepository { nameWithOwner }
    }
  }
}"""


class LedgerError(Exception):
    pass


class Unconfirmed(LedgerError):
    pass


class GuardUnavailable(LedgerError):
    pass


class CommentCapacityReached(LedgerError):
    pass


def positive_id(value):
    return type(value) is int and value > 0


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise LedgerError("duplicate JSON object key")
        result[key] = value
    return result


def decode_json(value):
    try:
        return json.loads(value, object_pairs_hook=unique_object)
    except (ValueError, TypeError, RecursionError) as error:
        raise LedgerError(f"invalid JSON: {error}") from error


def api(method, endpoint, payload=None):
    if method == "DELETE":
        return delete_api(endpoint, payload)
    command = ["gh", "api", "--method", method, endpoint]
    data = None
    if payload is not None:
        command += ["--input", "-"]
        data = json.dumps(payload)
    # Only fixed queries are proven read-only; a GraphQL POST may also mutate.
    read_only = (method == "GET" and endpoint != "graphql") or (
        method in ("GET", "POST") and endpoint == "graphql" and
        isinstance(payload, dict) and set(payload) <= {"query", "variables"} and
        payload.get("query") in (COMMENTS_QUERY, CLAIM_QUERY, PR_HEAD_QUERY))
    for attempt in range(len(READ_RETRY_DELAYS) + 1):
        try:
            result = subprocess.run(command, input=data, capture_output=True,
                                    text=True, timeout=60)
        except (OSError, subprocess.TimeoutExpired) as error:
            if read_only and isinstance(error, subprocess.TimeoutExpired) and \
                    attempt < len(READ_RETRY_DELAYS):
                time.sleep(READ_RETRY_DELAYS[attempt])
                continue
            raise LedgerError(f"GitHub request failed: {error}") from error
        if result.returncode:
            if method == "POST" and positive_id(LEDGER_NUMBER) and \
                    endpoint == f"repos/{KIT_REPO}/issues/{LEDGER_NUMBER}/comments" and \
                    result.stderr.strip() == f"gh: {COMMENT_CAPACITY_MESSAGE} (HTTP 403)":
                raise CommentCapacityReached(
                    "ledger comment capacity reached; no request submitted; maintainer action required")
            if read_only and attempt < len(READ_RETRY_DELAYS) and re.fullmatch(
                    r"gh: (?:HTTP (?:502|503|504)|[^\r\n]+ \(HTTP (?:502|503|504)\))",
                    result.stderr.strip()):
                time.sleep(READ_RETRY_DELAYS[attempt])
                continue
            raise LedgerError(f"GitHub request failed: {result.stderr.strip() or result.stdout.strip()}")
        return decode_json(result.stdout)


def endpoint(suffix=""):
    global LEDGER_NUMBER
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", KIT_REPO):
        raise LedgerError("invalid configured repository")
    if LEDGER_NUMBER is None:
        LEDGER_NUMBER = _resolve_ledger_number()
    if not positive_id(LEDGER_NUMBER):
        raise LedgerError("invalid configured ledger issue")
    return f"repos/{KIT_REPO}/issues/{LEDGER_NUMBER}{suffix}"


def _resolve_ledger_number():
    """Discover one owner-authored open ledger; an explicit pin must agree."""
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", KIT_REPO):
        raise LedgerError("invalid configured repository")
    override = os.environ.get("FFTA_LEDGER_ISSUE")
    if override is not None and not re.fullmatch(r"[1-9][0-9]*", override):
        raise LedgerError("FFTA_LEDGER_ISSUE must be a positive issue number")
    owner = KIT_REPO.split("/")[0].casefold()
    candidates = []
    seen = set()
    for page in range(1, 101):
        issues = api("GET", f"repos/{KIT_REPO}/issues?state=open&per_page=100&page={page}")
        if not isinstance(issues, list) or len(issues) > 100:
            raise LedgerError("invalid ledger discovery response")
        for issue in issues:
            if not isinstance(issue, dict) or not positive_id(issue.get("number")) or \
                    issue["number"] in seen:
                raise LedgerError("invalid or repeated issue in ledger discovery")
            seen.add(issue["number"])
            if issue.get("state") != "open" or "pull_request" in issue:
                continue
            title = issue.get("title")
            author = issue.get("user")
            if not isinstance(title, str) or title.strip().casefold() != LEDGER_TITLE or \
                    not isinstance(author, dict) or not isinstance(author.get("login"), str) or \
                    author["login"].casefold() != owner:
                continue
            if issue.get("repository_url") != f"https://api.github.com/repos/{KIT_REPO}":
                raise LedgerError("ledger discovery returned an unexpected repository")
            candidates.append(issue["number"])
        if len(issues) < 100:
            break
    else:
        raise LedgerError("ledger discovery exceeded its pagination limit")
    if len(candidates) != 1:
        raise LedgerError("expected exactly one owner-authored open address ledger")
    number = candidates[0]
    if override is not None and int(override) != number:
        raise LedgerError("FFTA_LEDGER_ISSUE does not match the authoritative open ledger")
    return number


def self_update():
    root = os.path.dirname(HERE)
    if not os.path.isdir(os.path.join(root, ".git")):
        return
    result = subprocess.run(["git", "-C", root, "pull", "--ff-only", "-q"],
                            capture_output=True, text=True)
    if result.returncode:
        print("note: could not update the kit; using the local rules: "
              + result.stderr.strip(), file=sys.stderr)


def now():
    return datetime.datetime.now(datetime.timezone.utc).replace(
        microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_ts(value):
    if not isinstance(value, str):
        raise LedgerError("invalid ledger timestamp")
    try:
        return datetime.datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=datetime.timezone.utc)
    except ValueError as error:
        raise LedgerError("invalid ledger timestamp") from error


def normalise(address):
    if not isinstance(address, str) or not re.fullmatch(r"0[xX][0-9A-Fa-f]{8}", address):
        raise LedgerError("address must be 0x followed by eight hex digits")
    value = int(address, 16)
    if not 0x08000000 <= value < 0x09000000 or value % 2:
        raise LedgerError("address must be halfword-aligned inside the 16 MiB ROM image [0x08000000, 0x09000000)")
    return f"0x{value:08X}"


def text_field(value, name, maximum=400, empty=True):
    if not isinstance(value, str) or len(value) > maximum or (not empty and not value.strip()):
        raise LedgerError(f"invalid {name}")
    if value != value.strip():
        raise LedgerError(f"outer whitespace in {name}")
    if any(ord(character) < 32 or ord(character) == 127 or 0xD800 <= ord(character) <= 0xDFFF
           or ord(character) in (0x85, 0x2028, 0x2029) for character in value):
        raise LedgerError(f"control characters in {name}")
    return value


def table_rows(body):
    if not isinstance(body, str) or body.count(START) != 1 or body.count(END) != 1:
        raise LedgerError("ledger table markers missing or ambiguous")
    start = body.index(START) + len(START)
    finish = body.index(END)
    if start > finish:
        raise LedgerError("ledger table markers out of order")
    content = body[start:finish]
    lines = [line.strip() for line in content.splitlines() if line.strip()]
    if len(lines) < 2:
        raise LedgerError("ledger table header missing")
    cells = lambda line: [html.unescape(cell.strip()) for cell in line.strip("|").split("|")]
    if cells(lines[0]) != ["address", "claimed by", "claimed at", "last seen", "note"]:
        raise LedgerError("unexpected ledger table header")
    if not re.fullmatch(r"\|\s*-+\s*\|\s*-+\s*\|\s*-+\s*\|\s*-+\s*\|\s*-+\s*\|", lines[1]):
        raise LedgerError("invalid ledger table separator")
    rows = []
    for line in lines[2:]:
        values = cells(line)
        if not line.startswith("|") or not line.endswith("|") or len(values) != 5:
            raise LedgerError("malformed ledger row")
        address, who, claimed_at, last_seen, note = values
        rows.append({"address": normalise(address), "who": who,
                     "claimed_at": claimed_at, "last_seen": last_seen,
                     "note": note, "owner_id": None, "claim_id": None})
    return rows


def validate_state(state):
    if not isinstance(state, dict) or set(state) != {"version", "cursor", "rows", "results"}:
        raise LedgerError("invalid broker state fields")
    if type(state["version"]) is not int or state["version"] != 1:
        raise LedgerError("unsupported broker state version")
    if type(state["cursor"]) is not int or state["cursor"] < 0:
        raise LedgerError("invalid broker cursor")
    if not isinstance(state["rows"], list) or len(state["rows"]) > MAX_ROWS:
        raise LedgerError("ledger row limit exceeded")
    addresses = set()
    claims = set()
    for row in state["rows"]:
        if not isinstance(row, dict) or set(row) != ROW_FIELDS:
            raise LedgerError("invalid row fields")
        if normalise(row["address"]) != row["address"] or row["address"] in addresses:
            raise LedgerError("duplicate or noncanonical row address")
        addresses.add(row["address"])
        text_field(row["who"], "lane", 64, empty=False)
        text_field(row["note"], "note")
        if parse_ts(row["last_seen"]) < parse_ts(row["claimed_at"]):
            raise LedgerError("lease timestamp predates claim")
        if row["owner_id"] is None and row["claim_id"] is None:
            continue
        if not positive_id(row["owner_id"]) or not positive_id(row["claim_id"]):
            raise LedgerError("invalid authenticated row identity")
        if row["claim_id"] > state["cursor"] or row["claim_id"] in claims:
            raise LedgerError("invalid or duplicate claim request ID")
        claims.add(row["claim_id"])
    if not isinstance(state["results"], list) or len(state["results"]) > MAX_RESULTS:
        raise LedgerError("invalid recent results")
    previous = 0
    for result in state["results"]:
        if not isinstance(result, dict) or set(result) != RESULT_FIELDS:
            raise LedgerError("invalid result fields")
        request_id = result["request_id"]
        if not positive_id(request_id) or not previous < request_id <= state["cursor"]:
            raise LedgerError("invalid result sequence")
        previous = request_id
        if not positive_id(result["owner_id"]):
            raise LedgerError("invalid result owner")
        if result["status"] not in ("accepted", "rejected"):
            raise LedgerError("invalid result status")
        if type(result["code"]) is not int or result["code"] not in (0, 1, 3, 4, 5):
            raise LedgerError("invalid result code")
        if (result["status"] == "accepted") != (result["code"] == 0):
            raise LedgerError("result code disagrees with status")
        text_field(result["message"], "result message")
        text_field(result["who"], "result lane", 64)
        if result["operation"] not in ("claim", "ping", "release", "invalid"):
            raise LedgerError("invalid result operation")
        if result["address"] is not None:
            normalise(result["address"])
        if result["claim_id"] is not None and not positive_id(result["claim_id"]):
            raise LedgerError("invalid result claim ID")
        if result["status"] == "accepted" and (result["operation"] == "invalid" or
                result["address"] is None or result["claim_id"] is None or not result["who"]):
            raise LedgerError("accepted result is missing its identity")


def parse_ledger(body):
    visible = table_rows(body)
    if STATE_START not in body and STATE_END not in body:
        if "ffta-ledger-state" in body:
            raise LedgerError("malformed broker state markers")
        state = {"version": 1, "cursor": 0, "rows": visible, "results": []}
    else:
        if body.count(STATE_START) != 1 or body.count(STATE_END) != 1:
            raise LedgerError("broker state markers missing or ambiguous")
        content = body.split(STATE_START)[1].split(STATE_END)
        if len(content) != 2:
            raise LedgerError("broker state markers out of order")
        state = decode_json(content[0])
        validate_state(state)
        projected = [{**row, "owner_id": None, "claim_id": None} for row in state["rows"]]
        if projected != visible:
            raise LedgerError("visible table differs from broker state; maintainer reconciliation required")
    validate_state(state)
    return state


def render(state):
    validate_state(state)
    lines = ["# Address ledger", "", "Reservations are accepted only by the trusted broker.",
             "Legacy rows have no authenticated owner; labels do not establish identity.",
             "", START, "| address | claimed by | claimed at | last seen | note |",
             "|---|---|---|---|---|"]
    for row in state["rows"]:
        values = [html.escape(str(row[field]), quote=False).replace("|", "&#124;")
                  for field in ("address", "who", "claimed_at", "last_seen", "note")]
        lines.append("| " + " | ".join(values) + " |")
    metadata = json.dumps(state, ensure_ascii=True, separators=(",", ":")).replace("<", "\\u003c").replace(">", "\\u003e")
    body = "\n".join(lines + [END, "", STATE_START + metadata + STATE_END, ""])
    if len(body.encode("utf-8")) > MAX_BODY_BYTES:
        raise LedgerError("ledger body capacity exceeded; maintainer reconciliation required")
    if parse_ledger(body) != state:
        raise LedgerError("rendered ledger does not preserve broker state")
    return body


def ledger():
    issue = api("GET", endpoint())
    if not isinstance(issue, dict) or issue.get("number") != int(LEDGER_NUMBER):
        raise LedgerError("configured ledger issue not found")
    if issue.get("state") != "open" or "pull_request" in issue:
        raise LedgerError("configured ledger must be an open issue, not a pull request")
    return issue, parse_ledger(issue.get("body"))


def held_by(state, address):
    return next((row for row in state["rows"] if row["address"] == address), None)


def unmatchable():
    try:
        with open(UNMATCHABLE_DB, encoding="utf-8") as source:
            records = decode_json(source.read())
    except FileNotFoundError:
        return set()
    if not isinstance(records, list) or any(not isinstance(record, dict) for record in records):
        raise LedgerError("invalid known-unmatchable database")
    return {normalise(record.get("address")) for record in records}


def decomp_query(query, **variables):
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", DECOMP_REPO):
        raise LedgerError("invalid configured decomp repository")
    owner, name = DECOMP_REPO.split("/")
    result = api("POST", "graphql", {"query": query,
                 "variables": dict(variables, owner=owner, name=name)})
    if not isinstance(result, dict) or result.get("errors"):
        raise LedgerError("decomp duplicate-check query failed")
    try:
        repository = result["data"]["repository"]
    except (KeyError, TypeError) as error:
        raise LedgerError("decomp repository is unavailable") from error
    if not isinstance(repository, dict):
        raise LedgerError("decomp repository is unavailable")
    return repository


def connection_page(connection):
    if not isinstance(connection, dict) or not isinstance(connection.get("nodes"), list):
        raise LedgerError("invalid duplicate-check connection")
    page = connection.get("pageInfo")
    if not isinstance(page, dict) or type(page.get("hasNextPage")) is not bool:
        raise LedgerError("invalid duplicate-check pagination")
    after = page.get("endCursor") if page["hasNextPage"] else None
    if page["hasNextPage"] and (not connection["nodes"] or not isinstance(after, str) or not after):
        raise LedgerError("missing duplicate-check pagination cursor")
    return connection["nodes"], after


def pull_head(pull):
    if not isinstance(pull, dict) or pull.get("state") != "OPEN":
        raise LedgerError("open PR changed during duplicate check")
    oid, repository = pull.get("headRefOid"), pull.get("headRepository")
    if not isinstance(oid, str) or re.fullmatch(r"[0-9a-f]{40}", oid) is None or \
            not isinstance(repository, dict) or \
            not isinstance(repository.get("nameWithOwner"), str) or \
            re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository["nameWithOwner"]) is None:
        raise LedgerError("open PR head repository or commit is unavailable")
    return repository["nameWithOwner"], oid


def git_tree_entries(repository, oid, recursive=False):
    suffix = "?recursive=1" if recursive else ""
    tree = api("GET", f"repos/{repository}/git/trees/{oid}{suffix}")
    if not isinstance(tree, dict) or tree.get("sha") != oid or \
            tree.get("truncated") is not False or not isinstance(tree.get("tree"), list):
        raise LedgerError("PR head source tree is unavailable, malformed or truncated")
    paths = set()
    modes = {"blob": {"100644", "100755", "120000"},
             "tree": {"040000"}, "commit": {"160000"}}
    for entry in tree["tree"]:
        if not isinstance(entry, dict):
            raise LedgerError("invalid PR head source-tree entry")
        path, kind, sha = entry.get("path"), entry.get("type"), entry.get("sha")
        if not isinstance(path, str) or not path or "\0" in path or \
                any(part in ("", ".", "..") for part in path.split("/")) or \
                (not recursive and "/" in path) or path in paths or \
                not isinstance(kind, str) or kind not in modes or \
                not isinstance(entry.get("mode"), str) or entry["mode"] not in modes[kind] or \
                not isinstance(sha, str) or \
                re.fullmatch(r"[0-9a-f]{40}", sha) is None:
            raise LedgerError("invalid PR head source-tree entry")
        paths.add(path)
    return tree["tree"]


def pr_has_source(pull, filename):
    """Inspect a pinned fork-aware source tree, never the capped PR file diff."""
    repository, head = pull_head(pull)
    commit = api("GET", f"repos/{repository}/git/commits/{head}")
    if not isinstance(commit, dict) or commit.get("sha") != head or \
            not isinstance(commit.get("tree"), dict):
        raise LedgerError("PR head commit is unavailable or changed")
    tree_oid = commit["tree"].get("sha")
    if not isinstance(tree_oid, str) or re.fullmatch(r"[0-9a-f]{40}", tree_oid) is None:
        raise LedgerError("PR head commit has no valid tree")
    entries = git_tree_entries(repository, tree_oid)
    source = next((entry for entry in entries if entry["path"] == "src"), None)
    found = False
    if source is not None:
        if source["type"] != "tree":
            raise LedgerError("PR head src is not a source tree")
        entries = git_tree_entries(repository, source["sha"], recursive=True)
        found = any(entry["type"] == "blob" and
                    entry["path"].rsplit("/", 1)[-1].casefold() == filename.casefold()
                    for entry in entries)
    current = decomp_query(PR_HEAD_QUERY, number=pull["number"]).get("pullRequest")
    if not isinstance(current, dict) or not positive_id(current.get("number")) or \
            current["number"] != pull["number"] or \
            pull_head(current) != (repository, head):
        raise LedgerError("open PR head changed during duplicate check")
    return found


def claim_status(address):
    try:
        address = normalise(address)
        filename = address[2:] + ".c"
        token = re.compile(r"(?<![A-Za-z0-9_])(?:0x|func_)?" + address[2:]
                           + r"(?![A-Za-z0-9_])", re.IGNORECASE)
        after = None
        seen = set()
        while True:
            repository = decomp_query(CLAIM_QUERY, after=after)
            branch = repository.get("defaultBranchRef")
            tree = repository.get("object")
            if not isinstance(branch, dict) or not isinstance(branch.get("name"), str):
                raise LedgerError("decomp default branch is unavailable")
            if not isinstance(tree, dict) or tree.get("__typename") != "Tree" or not isinstance(tree.get("entries"), list):
                raise LedgerError("default-branch src tree is unavailable")
            for entry in tree["entries"]:
                if not isinstance(entry, dict) or not isinstance(entry.get("name"), str) or not isinstance(entry.get("type"), str):
                    raise LedgerError("invalid default-branch src entry")
                if entry["name"] == filename:
                    return 4, f"MATCHED: src/{filename} is on the default branch"
            pulls, after = connection_page(repository.get("pullRequests"))
            for pull in pulls:
                if not isinstance(pull, dict) or not positive_id(pull.get("number")):
                    raise LedgerError("invalid open PR identity")
                title, body = pull.get("title"), pull.get("body")
                if not isinstance(title, str) or (body is not None and not isinstance(body, str)):
                    raise LedgerError("invalid open PR text")
                message = f"IN PR #{pull['number']}: address is already in review"
                if token.search(title + "\n" + (body or "")):
                    return 5, message
                if pr_has_source(pull, filename):
                    return 5, message
            if after is None:
                return 0, ""
            if after in seen:
                raise LedgerError("repeated open PR cursor")
            seen.add(after)
    except LedgerError as error:
        raise GuardUnavailable(f"duplicate guards unavailable; no claim accepted: {error}") from error


def parse_request(body):
    if not isinstance(body, str) or not body.startswith(REQUEST_PREFIX):
        return None
    try:
        length = len(body.encode("utf-8"))
    except UnicodeEncodeError as error:
        raise LedgerError("invalid request text encoding") from error
    if length > MAX_REQUEST_BYTES:
        raise LedgerError("request exceeds 2 KiB")
    request = decode_json(body[len(REQUEST_PREFIX):])
    if not isinstance(request, dict):
        raise LedgerError("request must be an object")
    operation = request.get("operation")
    common = {"operation", "address", "who"}
    fields = {"claim": common | {"note"}, "ping": common | {"claim_id"},
              "release": common | {"claim_id", "reason", "unmatchable", "tried"}}
    if not isinstance(operation, str) or operation not in fields or set(request) != fields[operation]:
        raise LedgerError("invalid request operation or fields")
    request["address"] = normalise(request["address"])
    text_field(request["who"], "lane", 64, empty=False)
    if operation == "claim":
        text_field(request["note"], "note")
    else:
        if not positive_id(request["claim_id"]):
            raise LedgerError("invalid claim request ID")
    if operation == "release":
        text_field(request["reason"], "reason")
        text_field(request["tried"], "tried")
        if type(request["unmatchable"]) is not bool:
            raise LedgerError("invalid unmatchable evidence flag")
    return request


def comment_identity(comment):
    if not isinstance(comment, dict) or not positive_id(comment.get("id")):
        raise LedgerError("invalid server comment identity")
    author = comment.get("user")
    if not isinstance(author, dict) or not positive_id(author.get("id")):
        raise LedgerError("invalid authenticated comment author")
    if author.get("type") not in ("User", "Bot"):
        raise LedgerError("unsupported authenticated comment author")
    return comment["id"], author["id"]


def apply_comment(state, comment, skipped, timestamp, claim_check=None):
    request_id, owner_id = comment_identity(comment)
    if request_id <= state["cursor"]:
        return state
    candidate = copy.deepcopy(state)
    candidate["cursor"] = request_id
    result = {"request_id": request_id, "owner_id": owner_id, "who": "",
              "operation": "invalid", "address": None, "claim_id": None,
              "status": "rejected", "code": 1, "message": "invalid request"}
    try:
        request = parse_request(comment.get("body"))
        if request is None:
            return candidate
        result.update({field: request[field] for field in ("who", "operation", "address")})
        operation = request["operation"]
        result["claim_id"] = request_id if operation == "claim" else request["claim_id"]
        row = held_by(candidate, request["address"])
        if operation == "claim":
            if row:
                raise LedgerError("address is already reserved")
            if request["address"] in skipped:
                result["code"] = 3
                raise LedgerError("address is recorded as unmatchable")
            if len(candidate["rows"]) >= MAX_ROWS:
                raise LedgerError("ledger row capacity reached")
            if claim_check is None:
                raise GuardUnavailable("authoritative duplicate guard is required for claims")
            code, message = claim_check(request["address"])
            if code:
                result["code"] = code
                raise LedgerError(message)
            candidate["rows"].append({"address": request["address"], "who": request["who"],
                                      "claimed_at": timestamp, "last_seen": timestamp,
                                      "note": request["note"] or "-", "owner_id": owner_id,
                                      "claim_id": request_id})
        else:
            if not row:
                raise LedgerError("address is not reserved")
            if row["owner_id"] is None:
                raise LedgerError("legacy ownership requires maintainer reconciliation")
            if (row["owner_id"], row["who"], row["claim_id"]) != (
                    owner_id, request["who"], request["claim_id"]):
                raise LedgerError("owner, lane, or claim request ID does not match")
            if operation == "ping":
                row["last_seen"] = timestamp
            else:
                candidate["rows"].remove(row)
        result["status"] = "accepted"
        result["code"] = 0
        result["message"] = operation + " accepted"
        if operation == "release" and request["unmatchable"]:
            result["message"] += "; unmatchable evidence requires maintainer review"
    except GuardUnavailable:
        raise
    except LedgerError as error:
        candidate["rows"] = copy.deepcopy(state["rows"])
        result["message"] = str(error)[:400]
    candidate["results"] = (candidate["results"] + [result])[-MAX_RESULTS:]
    try:
        render(candidate)
    except LedgerError:
        candidate["rows"] = copy.deepcopy(state["rows"])
        result["status"] = "rejected"
        result["code"] = 1
        result["message"] = "ledger capacity or validation failed; no change accepted"
        render(candidate)
    return candidate


def comments_after(cursor):
    endpoint()
    owner, name = KIT_REPO.split("/")
    comments = []
    after = None
    seen_cursors = set()
    while True:
        result = api("POST", "graphql", {"query": COMMENTS_QUERY,
                     "variables": {"owner": owner, "name": name,
                                   "issue": int(LEDGER_NUMBER), "after": after}})
        if not isinstance(result, dict) or result.get("errors"):
            raise LedgerError("GitHub comment query failed")
        try:
            connection = result["data"]["repository"]["issue"]["comments"]
            edges = connection["edges"]
            page_info = connection["pageInfo"]
        except (KeyError, TypeError) as error:
            raise LedgerError("configured ledger comment connection is unavailable") from error
        if not isinstance(edges, list) or not isinstance(page_info, dict):
            raise LedgerError("invalid comment connection")
        for edge in edges:
            if not isinstance(edge, dict) or not isinstance(edge.get("node"), dict):
                raise LedgerError("invalid comment node")
            node = edge["node"]
            database_id = node.get("fullDatabaseId")
            if isinstance(database_id, str) and re.fullmatch(r"[1-9][0-9]{0,19}", database_id):
                database_id = int(database_id)
            author = node.get("author")
            if not isinstance(author, dict) or not isinstance(node.get("body"), str):
                raise LedgerError("invalid server comment author or body")
            comment = {"id": database_id, "body": node["body"],
                       "user": {"id": author.get("databaseId"), "type": author.get("__typename")}}
            request_id, owner_id = comment_identity(comment)
            if request_id > cursor:
                comments.append(comment)
        has_next = page_info.get("hasNextPage")
        if type(has_next) is not bool:
            raise LedgerError("invalid comment pagination flag")
        if not has_next:
            break
        after = page_info.get("endCursor")
        if not edges or not isinstance(after, str) or not after or after in seen_cursors:
            raise LedgerError("invalid or repeated comment pagination cursor")
        if edges[-1].get("cursor") != after:
            raise LedgerError("comment connection cursor does not match its final edge")
        seen_cursors.add(after)
    identifiers = [comment["id"] for comment in comments]
    if len(identifiers) != len(set(identifiers)):
        raise LedgerError("comment listing changed during pagination; retry drain")
    return sorted(comments, key=lambda comment: comment["id"])


def persist(state, previous_body):
    body = render(state)
    current, current_state = ledger()
    if current["body"] != previous_body:
        raise LedgerError("ledger changed outside the serialized broker; refusing stale write")
    updated = api("PATCH", endpoint(), {"body": body})
    if not isinstance(updated, dict) or updated.get("body") != body:
        raise Unconfirmed("ledger write acknowledgement differs; retry the broker")
    return body


def delete_api(endpoint, payload=None):
    """Archive deletion is a single mutation; an empty HTTP 204 body succeeds."""
    command = ["gh", "api", "--method", "DELETE", endpoint]
    data = None
    if payload is not None:
        command += ["--input", "-"]
        data = json.dumps(payload)
    try:
        result = subprocess.run(command, input=data, capture_output=True,
                                text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise LedgerError(f"GitHub request failed: {error}") from error
    if result.returncode:
        raise LedgerError(f"GitHub request failed: {result.stderr.strip() or result.stdout.strip()}")
    return decode_json(result.stdout) if result.stdout.strip() else None


def archive_json(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, indent=2) + "\n"


def body_hash(body):
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def archive_oid(value):
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise LedgerError("invalid archive Git object identity")
    return value


def receipt_comment(request_id):
    try:
        comment = api("GET", f"repos/{KIT_REPO}/issues/comments/{request_id}")
    except LedgerError as error:
        if re.fullmatch(r"GitHub request failed: gh: [^\r\n]+ \(HTTP 404\)", str(error)):
            return None
        raise
    if not isinstance(comment, dict) or comment_identity(comment)[0] != request_id or \
            comment.get("issue_url") != f"https://api.github.com/repos/{KIT_REPO}/issues/{LEDGER_NUMBER}":
        raise LedgerError("archive comment does not belong to the ledger")
    snapshot = {key: comment.get(key) for key in
                ("id", "body", "created_at", "updated_at", "issue_url")}
    snapshot["user"] = {key: comment["user"].get(key) for key in ("id", "type")}
    if not isinstance(snapshot["body"], str) or \
            parse_ts(snapshot["updated_at"]) < parse_ts(snapshot["created_at"]):
        raise LedgerError("invalid archive comment snapshot")
    return snapshot


def validate_receipt(receipt, operation):
    if not isinstance(receipt, dict) or set(receipt) != {
            "comment", "result", "body_sha256", "body_provenance",
            "acceptance_body_sha256", "acknowledged_cursor", "ledger_body_sha256"}:
        raise LedgerError("invalid archived receipt fields")
    comment, result = receipt["comment"], receipt["result"]
    if not isinstance(comment, dict) or set(comment) != {
            "id", "body", "created_at", "updated_at", "issue_url", "user"}:
        raise LedgerError("invalid archived comment fields")
    request_id, owner_id = comment_identity(comment)
    request = parse_request(comment["body"])
    validate_state({"version": 1, "cursor": receipt["acknowledged_cursor"],
                    "rows": [], "results": [result]})
    if request is None or request["operation"] != operation or \
            comment["issue_url"] != f"https://api.github.com/repos/{KIT_REPO}/issues/{LEDGER_NUMBER}" or \
            parse_ts(comment["updated_at"]) < parse_ts(comment["created_at"]) or \
            receipt["body_sha256"] != body_hash(comment["body"]):
        raise LedgerError("archived comment identity or body differs")
    claim_id = request_id if operation == "claim" else request["claim_id"]
    expected = {"request_id": request_id, "owner_id": owner_id,
                "operation": operation, "address": request["address"],
                "who": request["who"], "claim_id": claim_id,
                "status": "accepted", "code": 0}
    expected_message = operation + " accepted"
    if operation == "release" and request["unmatchable"]:
        expected_message += "; unmatchable evidence requires maintainer review"
    if any(result[key] != value for key, value in expected.items()) or result["message"] != expected_message:
        raise LedgerError("archived request disagrees with authenticated acceptance")
    if not isinstance(receipt["ledger_body_sha256"], str) or \
            re.fullmatch(r"[0-9a-f]{64}", receipt["ledger_body_sha256"]) is None:
        raise LedgerError("invalid archived ledger snapshot hash")
    if receipt["body_provenance"] == "acceptance-time":
        if receipt["acceptance_body_sha256"] != receipt["body_sha256"]:
            raise LedgerError("acceptance-time body hash differs")
    elif receipt["body_provenance"] != "snapshot-at-archive" or \
            receipt["acceptance_body_sha256"] != "UNPROVEN":
        raise LedgerError("invalid legacy snapshot provenance")
    return request


def validate_generation(generation):
    if not isinstance(generation, dict) or set(generation) != {"claim", "release"}:
        raise LedgerError("invalid archived claim generation")
    claim = validate_receipt(generation["claim"], "claim")
    release = generation["release"]
    if release is not None:
        request = validate_receipt(release, "release")
        before, after = generation["claim"]["result"], release["result"]
        if after["request_id"] <= before["request_id"] or any(
                after[key] != before[key] for key in ("claim_id", "owner_id", "who", "address")):
            raise LedgerError("archived release is not the same authenticated generation")
        # Keep complete request bodies, including reason/tried/unmatchable, verbatim.
        if request["claim_id"] != before["request_id"]:
            raise LedgerError("archived release points at a different claim")
    return claim


class ReceiptArchive:
    """Trusted broker only. Git publication and readback precede every DELETE.

    pending.json journals accepted claims across the bounded ledger result window.
    Closed pairs are immutable per-generation files; pending entries remain until
    both comments are gone, so partial deletion and failed final writes can retry.
    """

    def __init__(self):
        endpoint()
        self.prefix = f"repos/{KIT_REPO}/git/"
        self.index_path = f"issues/{LEDGER_NUMBER}/pending.json"
        self.head = self.remote_head()
        if self.head is None:
            marker = self.write_blob(ARCHIVE_FORMAT)
            tree = api("POST", self.prefix + "trees", {"tree": [
                {"path": "archive.json", "type": "blob", "mode": "100644", "sha": marker}]})
            tree = archive_oid(tree.get("sha") if isinstance(tree, dict) else None)
            commit = api("POST", self.prefix + "commits", {
                "message": "Initialize trusted reservation receipt archive", "tree": tree, "parents": []})
            self.head = archive_oid(commit.get("sha") if isinstance(commit, dict) else None)
            api("POST", self.prefix + "refs", {"ref": ARCHIVE_REF, "sha": self.head})
            if self.remote_head() != self.head:
                raise LedgerError("archive initialization was not durably confirmed")
        commit = api("GET", self.prefix + "commits/" + self.head)
        if not isinstance(commit, dict) or commit.get("sha") != self.head:
            raise LedgerError("archive commit is unavailable")
        tree = commit.get("tree")
        self.tree = archive_oid(tree.get("sha") if isinstance(tree, dict) else None)
        self.files = self.read_tree(self.tree)
        if self.read("archive.json") != ARCHIVE_FORMAT:
            raise LedgerError("archive branch format is not recognized")
        self.index = self.read(self.index_path)
        if self.index is None:
            if self.index_path in self.files:
                raise LedgerError("archive pending index is not an object")
            self.index = {"version": 1, "repository": KIT_REPO, "issue": LEDGER_NUMBER, "generations": []}
        if not isinstance(self.index, dict) or set(self.index) != {
                "version", "repository", "issue", "generations"} or \
                self.index["version"] != 1 or self.index["repository"] != KIT_REPO or \
                self.index["issue"] != LEDGER_NUMBER or not isinstance(self.index["generations"], list) or \
                len(self.index["generations"]) > MAX_ROWS + MAX_RESULTS:
            raise LedgerError("invalid archive pending index")
        seen = set()
        for generation in self.index["generations"]:
            validate_generation(generation)
            claim_id = generation["claim"]["result"]["claim_id"]
            if claim_id in seen:
                raise LedgerError("duplicate archived claim generation")
            seen.add(claim_id)

    def remote_head(self):
        refs = api("GET", self.prefix + "matching-refs/" + ARCHIVE_REF.removeprefix("refs/"))
        if not isinstance(refs, list):
            raise LedgerError("archive ref listing is unavailable")
        matches = [item for item in refs if isinstance(item, dict) and item.get("ref") == ARCHIVE_REF]
        if len(matches) > 1:
            raise LedgerError("ambiguous archive ref")
        if not matches:
            return None
        target = matches[0].get("object", {})
        if not isinstance(target, dict) or target.get("type") != "commit":
            raise LedgerError("archive ref is not a commit")
        return archive_oid(target.get("sha"))

    def read_tree(self, oid):
        tree = api("GET", self.prefix + "trees/" + oid + "?recursive=1")
        if not isinstance(tree, dict) or tree.get("sha") != oid or \
                tree.get("truncated") is not False or not isinstance(tree.get("tree"), list):
            raise LedgerError("archive tree is unavailable or truncated")
        entries = {}
        for item in tree["tree"]:
            if not isinstance(item, dict) or not isinstance(item.get("path"), str):
                raise LedgerError("invalid archive tree entry")
            path = item["path"]
            if not path or "\0" in path or path in entries or \
                    any(part in ("", ".", "..") for part in path.split("/")) or \
                    (item.get("type"), item.get("mode")) not in (("blob", "100644"), ("tree", "040000")):
                raise LedgerError("invalid archive tree path or mode")
            archive_oid(item.get("sha"))
            entries[path] = {key: item[key] for key in ("path", "type", "mode", "sha")}
        return entries

    def read(self, path):
        entry = self.files.get(path)
        if entry is None:
            return None
        if entry["type"] != "blob" or entry["mode"] != "100644":
            raise LedgerError("archive receipt is not an ordinary Git blob")
        blob = api("GET", self.prefix + "blobs/" + entry["sha"])
        if not isinstance(blob, dict) or blob.get("sha") != entry["sha"] or blob.get("encoding") != "base64":
            raise LedgerError("archive blob readback is unavailable")
        try:
            data = base64.b64decode("".join(blob["content"].split()), validate=True)
            oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            if oid != entry["sha"]:
                raise LedgerError("archive blob identity differs")
            return decode_json(data.decode("utf-8"))
        except (ValueError, KeyError, UnicodeError, TypeError) as error:
            raise LedgerError("invalid archive blob content") from error

    def closed_path(self, generation):
        return f"issues/{LEDGER_NUMBER}/closed/{generation['claim']['result']['claim_id']}.json"

    def write_blob(self, value):
        content = archive_json(value)
        oid = hashlib.sha1(b"blob " + str(len(content.encode())).encode() + b"\0" + content.encode()).hexdigest()
        blob = api("POST", self.prefix + "blobs", {"content": content, "encoding": "utf-8"})
        if not isinstance(blob, dict) or blob.get("sha") != oid:
            raise LedgerError("archive blob publication was not confirmed")
        return oid

    def publish(self, changes):
        changes = {path: value for path, value in changes.items() if self.read(path) != value}
        if not changes:
            if self.remote_head() != self.head:
                raise LedgerError("archive ref changed outside the serialized broker")
            return
        entries = []
        for path, value in changes.items():
            oid = self.write_blob(value)
            entries.append({"path": path, "mode": "100644", "type": "blob", "sha": oid})
        tree = api("POST", self.prefix + "trees", {"base_tree": self.tree, "tree": entries})
        tree = archive_oid(tree.get("sha") if isinstance(tree, dict) else None)
        commit = api("POST", self.prefix + "commits", {
            "message": f"Preserve authenticated ledger #{LEDGER_NUMBER} receipts", "tree": tree, "parents": [self.head]})
        commit = archive_oid(commit.get("sha") if isinstance(commit, dict) else None)
        if self.remote_head() != self.head:
            raise LedgerError("archive ref conflict; no comments deleted")
        api("PATCH", self.prefix + "refs/" + ARCHIVE_REF.removeprefix("refs/"), {"sha": commit, "force": False})
        if self.remote_head() != commit:
            raise LedgerError("archive publication is uncertain; no comments deleted")
        published = api("GET", self.prefix + "commits/" + commit)
        parents = published.get("parents") if isinstance(published, dict) else None
        if not isinstance(published, dict) or published.get("sha") != commit or \
                not isinstance(published.get("tree"), dict) or published["tree"].get("sha") != tree or \
                not isinstance(parents, list) or len(parents) != 1 or \
                not isinstance(parents[0], dict) or parents[0].get("sha") != self.head:
            raise LedgerError("archive commit readback differs; no comments deleted")
        files = self.read_tree(tree)
        expected = {path: entry for path, entry in self.files.items()
                    if entry["type"] == "blob" and path not in changes}
        expected.update({entry["path"]: entry for entry in entries})
        if any(files.get(path) != entry for path, entry in expected.items()):
            raise LedgerError("published archive tree differs; no comments deleted")
        self.head, self.tree, self.files = commit, tree, files
        for path, value in changes.items():
            if self.read(path) != value:
                raise LedgerError("archive receipt readback differs; no comments deleted")

    def capture(self, state, acceptance_bodies=None):
        validate_state(state)
        acceptance_bodies = acceptance_bodies or {}
        updated = copy.deepcopy(self.index)
        generations = {item["claim"]["result"]["claim_id"]: item for item in updated["generations"]}
        for result in state["results"]:
            if result["status"] != "accepted" or result["code"] != 0 or result["operation"] not in ("claim", "release"):
                continue
            claim_id, operation = result["claim_id"], result["operation"]
            generation = generations.get(claim_id)
            if (operation == "claim" and generation) or (operation == "release" and
                    (generation is None or generation["release"] is not None)):
                continue
            snapshot = receipt_comment(result["request_id"])
            if snapshot is None:
                continue
            applied_body = acceptance_bodies.get(result["request_id"])
            if applied_body is not None and applied_body != snapshot["body"]:
                raise LedgerError("request body changed after broker acceptance")
            receipt = {"comment": snapshot, "result": copy.deepcopy(result),
                       "body_sha256": body_hash(snapshot["body"]),
                       "body_provenance": "acceptance-time" if applied_body is not None else "snapshot-at-archive",
                       "acceptance_body_sha256": body_hash(applied_body) if applied_body is not None else "UNPROVEN",
                       "acknowledged_cursor": state["cursor"], "ledger_body_sha256": body_hash(render(state))}
            # Mismatched/edited control fields cannot authorize archival.
            validate_receipt(receipt, operation)
            if operation == "claim":
                generations[claim_id] = {"claim": receipt, "release": None}
            else:
                generation["release"] = receipt
                validate_generation(generation)
        active_claims = {row["claim_id"] for row in state["rows"]}
        updated["generations"] = [item for key, item in sorted(generations.items())
                                  if item["release"] is not None or key in active_claims]
        if len(updated["generations"]) > MAX_ROWS + MAX_RESULTS:
            raise LedgerError("archive pending index bound exceeded; no comments deleted")
        changes = {self.index_path: updated}
        for generation in updated["generations"]:
            if generation["release"] is not None:
                path = self.closed_path(generation)
                old = self.read(path)
                if path in self.files and old != generation:
                    raise LedgerError("immutable closed receipt differs")
                changes[path] = generation
        self.publish(changes)
        self.index = updated

    def retire(self, state):
        validate_state(state)
        selected = [item for item in self.index["generations"] if item["release"] is not None
                    and item["release"]["result"]["request_id"] < state["cursor"]
                    and not held_by(state, item["claim"]["result"]["address"])][:ARCHIVE_BATCH]
        completed = []
        for generation in selected:
            validate_generation(generation)
            if any(generation[key]["acknowledged_cursor"] > state["cursor"] for key in ("claim", "release")):
                raise LedgerError("ledger cursor predates archived acceptance; no comments deleted")
            if self.read(self.closed_path(generation)) != generation or self.remote_head() != self.head:
                raise LedgerError("closed receipt publication no longer confirmed; no comments deleted")
            issue, current = ledger()
            if current != state:
                raise LedgerError("ledger changed before archive deletion; no comments deleted")
            snapshots = [receipt_comment(generation[key]["comment"]["id"]) for key in ("claim", "release")]
            if any(snapshot is not None and snapshot != generation[key]["comment"]
                   for key, snapshot in zip(("claim", "release"), snapshots)):
                raise LedgerError("comment changed since archive snapshot; no comments deleted")
            if self.remote_head() != self.head or ledger()[1] != state:
                raise LedgerError("archive or ledger changed before deletion; no comments deleted")
            # A missing member is allowed only here, after the complete pair was
            # published and read back: a previous deletion may have succeeded.
            for snapshot in reversed(snapshots):
                if snapshot is not None:
                    api("DELETE", f"repos/{KIT_REPO}/issues/comments/{snapshot['id']}")
            for key in ("claim", "release"):
                if receipt_comment(generation[key]["comment"]["id"]) is not None:
                    raise LedgerError("comment deletion is unconfirmed; retry the broker")
            completed.append(generation)
        if completed:
            updated = copy.deepcopy(self.index)
            updated["generations"] = [item for item in updated["generations"] if item not in completed]
            self.publish({self.index_path: updated})
            self.index = updated
        print(f"archived {len(completed)} closed reservation pair(s) to {ARCHIVE_REF}")


def drain(days=STALE_DAYS, archive_closed=False):
    issue, state = ledger()
    body = issue["body"]
    skipped = unmatchable()
    archive = ReceiptArchive() if archive_closed else None
    if archive:
        archive.capture(state)
        archive.retire(state)
    processed = 0
    acceptance_bodies = {}
    while True:
        comments = comments_after(state["cursor"])
        if not comments:
            break
        for comment in comments:
            candidate = apply_comment(state, comment, skipped, now(), claim_check=claim_status)
            body = persist(candidate, body)
            state = candidate
            acceptance_bodies[comment["id"]] = comment["body"]
            processed += 1
            if archive and processed % ARCHIVE_BATCH == 0:
                archive.capture(state, acceptance_bodies)
                archive.retire(state)
                acceptance_bodies.clear()
    if archive:
        archive.capture(state, acceptance_bodies)
        archive.retire(state)
    timestamp = now()
    cutoff = parse_ts(timestamp) - datetime.timedelta(days=days)
    candidate = copy.deepcopy(state)
    candidate["rows"] = [row for row in candidate["rows"]
                         if parse_ts(row["last_seen"]) > cutoff]
    dropped = len(state["rows"]) - len(candidate["rows"])
    if dropped:
        persist(candidate, body)
    print(f"drained {processed} comment(s); expired {dropped} lease(s)")
    return 0


def trusted_event():
    global LEDGER_NUMBER
    if os.environ.get("GITHUB_ACTIONS") != "true" or os.environ.get("GITHUB_REPOSITORY") != KIT_REPO:
        raise LedgerError("broker runs only in the trusted repository workflow")
    try:
        with open(os.environ["GITHUB_EVENT_PATH"], encoding="utf-8") as source:
            event = decode_json(source.read())
    except (KeyError, OSError) as error:
        raise LedgerError("trusted workflow event is unavailable") from error
    if not isinstance(event, dict) or not isinstance(event.get("repository"), dict):
        raise LedgerError("invalid trusted workflow event")
    repository = event["repository"]
    branch = repository.get("default_branch")
    if repository.get("full_name") != KIT_REPO or not isinstance(branch, str):
        raise LedgerError("unexpected workflow repository")
    if os.environ.get("GITHUB_REF") != "refs/heads/" + branch:
        raise LedgerError("broker must run from the default branch")
    LEDGER_NUMBER = _resolve_ledger_number()
    event_name = os.environ.get("GITHUB_EVENT_NAME")
    if event_name == "issue_comment":
        issue = event.get("issue", {})
        if not isinstance(issue, dict) or event.get("action") != "created" or \
                not positive_id(issue.get("number")) or issue["number"] != LEDGER_NUMBER or \
                issue.get("state") != "open" or \
                "pull_request" in issue:
            raise LedgerError("unexpected ledger comment event")
    elif event_name not in ("schedule", "workflow_dispatch"):
        raise LedgerError("unsupported broker event")
    inputs = event.get("inputs") or {}
    if not isinstance(inputs, dict):
        raise LedgerError("invalid workflow inputs")
    days = str(inputs.get("days", STALE_DAYS))
    if not days.isdigit() or not 1 <= int(days) <= 30:
        raise LedgerError("sweep days must be between 1 and 30")
    return int(days)


def identity():
    account = api("GET", "user")
    if not isinstance(account, dict) or not positive_id(account.get("id")):
        raise LedgerError("authenticated GitHub identity unavailable")
    return account["id"]


def acknowledged(state, request, request_id, owner_id):
    result = next((entry for entry in state["results"] if entry["request_id"] == request_id), None)
    if result is None:
        if state["cursor"] >= request_id:
            raise Unconfirmed("request result is no longer retained; ownership is unconfirmed")
        return None
    expected_claim = request_id if request["operation"] == "claim" else request["claim_id"]
    expected = {"owner_id": owner_id, "who": request["who"], "operation": request["operation"],
                "address": request["address"], "claim_id": expected_claim}
    if any(result[field] != value for field, value in expected.items()):
        raise Unconfirmed("persisted request identity differs; ownership is unconfirmed")
    if result["status"] == "rejected":
        return result
    row = held_by(state, request["address"])
    if request["operation"] in ("claim", "ping"):
        if not row or (row["owner_id"], row["who"], row["claim_id"]) != (
                owner_id, request["who"], expected_claim):
            raise Unconfirmed("accepted lease is no longer held; ownership is unconfirmed")
    elif row and row["claim_id"] == expected_claim:
        raise Unconfirmed("release result conflicts with the current row")
    return result


def submit(args):
    address = normalise(args.addr)
    issue, state = ledger()
    comments = issue.get("comments")
    if type(comments) is int and comments >= MAX_ISSUE_COMMENTS:
        raise CommentCapacityReached(
            f"ledger comment capacity reached ({comments}/{MAX_ISSUE_COMMENTS}); "
            "no request submitted; maintainer action required")
    row = held_by(state, address)
    if args.cmd == "claim":
        if row:
            print(f"TAKEN {address} by {row['who']}; no request submitted")
            return 1
        if address in unmatchable():
            print(f"SKIP {address}: recorded unmatchable; no request submitted")
            return 3
        code, message = claim_status(address)
        if code:
            print(message + "; no request submitted")
            return code
    owner_id = identity()
    who = args.who
    if args.cmd != "claim":
        if not row or row["owner_id"] is None:
            raise LedgerError("no authenticated lease; legacy ownership requires maintainer reconciliation")
        if row["owner_id"] != owner_id:
            raise LedgerError("lease belongs to a different authenticated actor")
        who = who or row["who"]
        claim_id = args.claim_id if args.claim_id is not None else row["claim_id"]
        if who != row["who"] or claim_id != row["claim_id"]:
            raise LedgerError("lane or claim request ID does not match the current lease")
    request = {"operation": args.cmd, "address": address, "who": who or "agent"}
    if args.cmd == "claim":
        request["note"] = args.note
    else:
        request["claim_id"] = claim_id
    if args.cmd == "release":
        request.update(reason=args.reason, unmatchable=args.unmatchable, tried=args.tried)
    body = REQUEST_PREFIX + json.dumps(request, ensure_ascii=True, separators=(",", ":"))
    parse_request(body)
    try:
        comment = api("POST", endpoint("/comments"), {"body": body})
        request_id, author_id = comment_identity(comment)
    except CommentCapacityReached:
        raise
    except LedgerError as error:
        raise Unconfirmed(f"request submission could not be confirmed; inspect the ledger before retrying: {error}") from error
    if author_id != owner_id:
        raise Unconfirmed("submitted request author differs from authenticated identity")
    print(f"request {request_id} submitted to ledger #{LEDGER_NUMBER}; not yet accepted")
    deadline = time.monotonic() + args.wait
    while True:
        try:
            current_issue, current_state = ledger()
            result = acknowledged(current_state, request, request_id, owner_id)
        except LedgerError as error:
            raise Unconfirmed(f"request {request_id} acknowledgement unavailable: {error}") from error
        if result is not None:
            print(f"{result['status'].upper()} {address}: {result['message']} (request {request_id})")
            return result["code"]
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise Unconfirmed(f"request {request_id} timed out unconfirmed; do not begin work or assume release")
        time.sleep(min(2, remaining))


def inspect(args):
    issue, state = ledger()
    if args.cmd == "check":
        address = normalise(args.addr)
        row = held_by(state, address)
        if row:
            owner = row["owner_id"] if row["owner_id"] is not None else "legacy/unverified"
            print(f"TAKEN {address} by {row['who']} (actor {owner}, claim {row['claim_id']})")
            return 1
        code, message = claim_status(address)
        if code:
            print(message)
            return code
        if address in unmatchable():
            print(f"SKIP {address}: recorded unmatchable")
            return 3
        print(f"FREE {address}; a successful broker claim is required before work")
        return 0
    for row in state["rows"]:
        owner = row["owner_id"] if row["owner_id"] is not None else "legacy/unverified"
        print(f"{row['address']} {row['who']} actor={owner} claim={row['claim_id']} last_seen={row['last_seen']} {row['note']}")
    if not state["rows"]:
        print("no reservations")
    print(f"ledger #{LEDGER_NUMBER}; processed through comment {state['cursor']}")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--no-pull", action="store_true", help="skip the automatic kit update")
    commands = parser.add_subparsers(dest="cmd", required=True)
    for operation in ("claim", "ping", "release"):
        command = commands.add_parser(operation)
        command.add_argument("addr")
        command.add_argument("--who", default=os.environ.get("FFTA_WHO"), help="agent lane, separate from authenticated ownership")
        command.add_argument("--wait", type=float, default=120, help="seconds to wait for a persisted broker acknowledgement (0..300)")
        if operation == "claim":
            command.add_argument("--note", default="")
            command.add_argument("--decomp-root", help="accepted for compatibility; metadata is not trusted for authorization")
        else:
            command.add_argument("--claim-id", type=int, help="expected original claim request ID")
        if operation == "release":
            command.add_argument("--reason", default="")
            command.add_argument("--unmatchable", action="store_true", help="submit evidence for maintainer review; never changes the database")
            command.add_argument("--tried", default="")
    command = commands.add_parser("check")
    command.add_argument("addr")
    commands.add_parser("list")
    command = commands.add_parser("broker", help="trusted workflow only: drain requests and expire stale rows")
    command.add_argument("--archive-closed", action="store_true",
                         help="trusted workflow only: publish closed receipts to Git before deleting comments")
    args = parser.parse_args()
    try:
        if args.cmd == "broker":
            return drain(trusted_event(), archive_closed=args.archive_closed)
        if hasattr(args, "wait") and not 0 <= args.wait <= 300:
            raise LedgerError("wait must be between 0 and 300 seconds")
        if not args.no_pull:
            self_update()
        if args.cmd in ("check", "list"):
            return inspect(args)
        return submit(args)
    except Unconfirmed as error:
        print(f"UNCONFIRMED: {error}", file=sys.stderr)
        return 6
    except (LedgerError, OSError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
