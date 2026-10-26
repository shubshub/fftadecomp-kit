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
Unmatchable evidence stays in the request comment for maintainer review; this
tool never writes repository contents or creates issues.
"""

import argparse
import copy
import datetime
import html
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
        number title body
        files(first:100) { nodes { path } pageInfo { hasNextPage endCursor } }
      }
      pageInfo { hasNextPage endCursor }
    }
  }
}"""
PR_FILES_QUERY = """query($owner:String!, $name:String!, $number:Int!, $after:String) {
  repository(owner:$owner, name:$name) {
    pullRequest(number:$number) {
      files(first:100, after:$after) { nodes { path } pageInfo { hasNextPage endCursor } }
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
    command = ["gh", "api", "--method", method, endpoint]
    data = None
    if payload is not None:
        command += ["--input", "-"]
        data = json.dumps(payload)
    # Only fixed queries are proven read-only; a GraphQL POST may also mutate.
    read_only = (method == "GET" and endpoint != "graphql") or (
        method in ("GET", "POST") and endpoint == "graphql" and
        isinstance(payload, dict) and set(payload) <= {"query", "variables"} and
        payload.get("query") in (COMMENTS_QUERY, CLAIM_QUERY, PR_FILES_QUERY))
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
                files = pull.get("files")
                seen_files = set()
                while True:
                    paths, file_after = connection_page(files)
                    for changed in paths:
                        if not isinstance(changed, dict) or not isinstance(changed.get("path"), str):
                            raise LedgerError("invalid PR changed-file path")
                        if changed["path"].lower() == ("src/" + filename).lower():
                            return 5, message
                    if file_after is None:
                        break
                    if file_after in seen_files:
                        raise LedgerError("repeated PR file cursor")
                    seen_files.add(file_after)
                    current = decomp_query(PR_FILES_QUERY, number=pull["number"], after=file_after).get("pullRequest")
                    if not isinstance(current, dict):
                        raise LedgerError("open PR changed during duplicate check")
                    files = current.get("files")
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


def drain(days=STALE_DAYS):
    issue, state = ledger()
    body = issue["body"]
    skipped = unmatchable()
    processed = 0
    while True:
        comments = comments_after(state["cursor"])
        if not comments:
            break
        for comment in comments:
            candidate = apply_comment(state, comment, skipped, now(), claim_check=claim_status)
            body = persist(candidate, body)
            state = candidate
            processed += 1
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
    commands.add_parser("broker", help="trusted workflow only: drain requests and expire stale rows")
    args = parser.parse_args()
    try:
        if args.cmd == "broker":
            return drain(trusted_event())
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
