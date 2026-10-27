import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import call, patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import reserve


ADDRESS = "0x08011040"
TIMESTAMP = "2026-10-26T00:00:00Z"
MISSING = object()


class FakeAPI:
    def __init__(self, comments=2499, operation="claim", post=None,
                 acknowledge=True, fail_ack=False):
        self.comments = comments
        self.post = post
        self.acknowledge = acknowledge
        self.fail_ack = fail_ack
        self.calls = []
        self.reads = 0
        self.state = {"version": 1, "cursor": 50, "rows": [], "results": []}
        if operation != "claim":
            self.state["rows"].append({
                "address": ADDRESS, "who": "lane", "claimed_at": TIMESTAMP,
                "last_seen": TIMESTAMP, "note": "-", "owner_id": 7,
                "claim_id": 50})

    def __call__(self, method, endpoint, payload=None):
        self.calls.append((method, endpoint, payload))
        ledger_endpoint = reserve.endpoint()
        if (method, endpoint) == ("GET", ledger_endpoint):
            self.reads += 1
            if self.fail_ack and self.reads > 1:
                raise reserve.LedgerError("acknowledgement connection failed")
            issue = {"number": 66, "state": "open",
                     "body": reserve.render(self.state)}
            if self.comments is not MISSING:
                issue["comments"] = self.comments
            return issue
        if (method, endpoint) == ("GET", "user"):
            return {"id": 7}
        if (method, endpoint) == ("POST", ledger_endpoint + "/comments"):
            if self.post is not None:
                return self.post(method, endpoint, payload)
            comment = {"id": 100, "user": {"id": 7, "type": "User"},
                       "body": payload["body"]}
            if self.acknowledge:
                self.state = reserve.apply_comment(
                    self.state, comment, set(), TIMESTAMP,
                    claim_check=lambda address: (0, "FREE"))
            return comment
        raise AssertionError(f"unexpected API call: {method} {endpoint}")


class ReservationCapacityTests(unittest.TestCase):
    def run_client(self, fake, operation="claim"):
        arguments = ["reserve.py", "--no-pull", operation]
        if operation != "list":
            arguments.append(ADDRESS)
        if operation in ("claim", "ping", "release"):
            arguments += ["--who", "lane", "--wait", "0"]
        output, errors = io.StringIO(), io.StringIO()
        with patch.object(reserve, "LEDGER_NUMBER", 66), \
                patch.object(reserve, "api", side_effect=fake), \
                patch.object(reserve, "claim_status", return_value=(0, "FREE")), \
                patch.object(reserve, "unmatchable", return_value=set()), \
                patch.object(reserve, "self_update") as update, \
                patch.object(sys, "argv", arguments), \
                contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            code = reserve.main()
        update.assert_not_called()
        return code, output.getvalue(), errors.getvalue()

    def test_capacity_preflight_blocks_each_request_without_posting(self):
        for operation in ("claim", "ping", "release"):
            for comments in (2500, 2501, 3000):
                with self.subTest(operation=operation, comments=comments):
                    fake = FakeAPI(comments, operation)
                    code, output, errors = self.run_client(fake, operation)
                    self.assertEqual(code, 2)
                    self.assertIn("ERROR: ledger comment capacity reached", errors)
                    self.assertIn("no request submitted", errors)
                    self.assertNotIn("UNCONFIRMED", errors)
                    self.assertEqual(output, "")
                    self.assertEqual(len(fake.calls), 1)
                    self.assertEqual(fake.calls[0][0], "GET")

    def test_below_capacity_preserves_authenticated_acceptance(self):
        for operation in ("claim", "ping", "release"):
            with self.subTest(operation=operation):
                fake = FakeAPI(2499, operation)
                code, output, errors = self.run_client(fake, operation)
                self.assertEqual(code, 0)
                self.assertIn("ACCEPTED", output)
                self.assertEqual(errors, "")
                self.assertEqual([call[0] for call in fake.calls],
                                 ["GET", "GET", "POST", "GET"])

    def test_only_server_integer_counts_trigger_preflight(self):
        for comments in (MISSING, None, "2500", 2500.0, True):
            with self.subTest(comments=comments):
                fake = FakeAPI(comments)
                code, output, errors = self.run_client(fake)
                self.assertEqual(code, 0)
                self.assertIn("ACCEPTED", output)
                self.assertEqual(errors, "")
                self.assertEqual(sum(call[0] == "POST" for call in fake.calls), 1)

    def test_read_only_commands_remain_available_at_capacity(self):
        for operation in ("list", "check"):
            with self.subTest(operation=operation):
                fake = FakeAPI(2500)
                code, output, errors = self.run_client(fake, operation)
                self.assertEqual(code, 0)
                self.assertTrue(output)
                self.assertEqual(errors, "")
                self.assertEqual([call[0] for call in fake.calls], ["GET"])

    def test_exact_post_capacity_race_is_definite_refusal_without_retry(self):
        real_api = reserve.api
        refusal = subprocess.CompletedProcess(
            [], 1, json.dumps({"message": reserve.COMMENT_CAPACITY_MESSAGE,
                               "status": "403"}),
            f"gh: {reserve.COMMENT_CAPACITY_MESSAGE} (HTTP 403)\n")
        for operation in ("claim", "ping", "release"):
            with self.subTest(operation=operation):
                fake = FakeAPI(2499, operation, post=real_api)
                with patch.object(reserve.subprocess, "run", return_value=refusal) as run:
                    code, output, errors = self.run_client(fake, operation)
                self.assertEqual(code, 2)
                self.assertIn("no request submitted", errors)
                self.assertNotIn("UNCONFIRMED", errors)
                self.assertEqual(output, "")
                self.assertEqual([call[0] for call in fake.calls], ["GET", "GET", "POST"])
                run.assert_called_once()
                self.assertEqual(run.call_args.args[0][:4],
                                 ["gh", "api", "--method", "POST"])

    def test_other_post_failures_remain_unconfirmed(self):
        real_api = reserve.api
        for message in (
                "gh: HTTP 504",
                "gh: Bad Gateway (HTTP 502)",
                "gh: Service Unavailable (HTTP 503)",
                "gh: Gateway Timeout (HTTP 504)",
                "gh: Resource not accessible by integration (HTTP 403)",
                f"gh: {reserve.COMMENT_CAPACITY_MESSAGE} (HTTP 422)",
                f"gh: {reserve.COMMENT_CAPACITY_MESSAGE}. (HTTP 403)",
                f"gh: {reserve.COMMENT_CAPACITY_MESSAGE} (HTTP 403)\nconnection lost",
                "error connecting to api.github.com"):
            with self.subTest(message=message):
                fake = FakeAPI(post=real_api)
                result = subprocess.CompletedProcess([], 1, "", message)
                with patch.object(reserve.subprocess, "run", return_value=result) as run:
                    code, output, errors = self.run_client(fake)
                self.assertEqual(code, 6)
                self.assertIn("UNCONFIRMED", errors)
                self.assertNotIn("no request submitted", errors)
                self.assertEqual(output, "")
                self.assertEqual(fake.reads, 1)
                run.assert_called_once()

    def test_capacity_refusal_is_scoped_to_posting_on_the_current_ledger(self):
        result = subprocess.CompletedProcess(
            [], 1, "", f"gh: {reserve.COMMENT_CAPACITY_MESSAGE} (HTTP 403)")
        with patch.object(reserve, "LEDGER_NUMBER", 66), \
                patch.object(reserve.subprocess, "run", return_value=result):
            for method, suffix in (("GET", "/66/comments"),
                                   ("PATCH", "/66/comments"),
                                   ("POST", "/67/comments"),
                                   ("POST", "/66")):
                with self.subTest(method=method, suffix=suffix):
                    with self.assertRaises(reserve.LedgerError) as caught:
                        reserve.api(method, f"repos/{reserve.KIT_REPO}/issues{suffix}")
                    self.assertNotIsInstance(caught.exception, reserve.CommentCapacityReached)

    def test_transport_exceptions_remain_unconfirmed(self):
        real_api = reserve.api
        for error in (OSError("connection lost"), subprocess.TimeoutExpired("gh", 60)):
            with self.subTest(error=error):
                fake = FakeAPI(post=real_api)
                with patch.object(reserve.subprocess, "run", side_effect=error) as run:
                    code, output, errors = self.run_client(fake)
                self.assertEqual(code, 6)
                self.assertIn("UNCONFIRMED", errors)
                self.assertEqual(output, "")
                run.assert_called_once()

    def test_successful_post_with_invalid_response_remains_unconfirmed(self):
        real_api = reserve.api
        for response in ("not JSON", json.dumps({"id": 100, "user": {"id": 0}})):
            with self.subTest(response=response):
                fake = FakeAPI(post=real_api)
                result = subprocess.CompletedProcess([], 0, response, "")
                with patch.object(reserve.subprocess, "run", return_value=result) as run:
                    code, output, errors = self.run_client(fake)
                self.assertEqual(code, 6)
                self.assertIn("UNCONFIRMED", errors)
                self.assertEqual(output, "")
                run.assert_called_once()

    def test_missing_acknowledgement_stays_unconfirmed_after_submission(self):
        for fake in (FakeAPI(acknowledge=False), FakeAPI(fail_ack=True)):
            with self.subTest(fail_ack=fake.fail_ack):
                code, output, errors = self.run_client(fake)
                self.assertEqual(code, 6)
                self.assertIn("request 100 submitted", output)
                self.assertIn("UNCONFIRMED", errors)
                self.assertEqual(sum(call[0] == "POST" for call in fake.calls), 1)

    def test_exhausted_read_retries_preserve_preflight_and_acknowledgement_exits(self):
        real_api = reserve.api
        failure = subprocess.CompletedProcess([], 1, "", "gh: HTTP 504")
        for fail_ack in (False, True):
            with self.subTest(fail_ack=fail_ack):
                fake = FakeAPI()

                def request(method, endpoint, payload=None):
                    if method == "GET" and endpoint == reserve.endpoint() and (
                            not fail_ack or fake.reads):
                        return real_api(method, endpoint, payload)
                    return fake(method, endpoint, payload)

                with patch.object(reserve.subprocess, "run", return_value=failure) as run, \
                        patch.object(reserve.time, "sleep") as sleep:
                    code, output, errors = self.run_client(request)
                self.assertEqual(code, 6 if fail_ack else 2)
                self.assertEqual(sum(item[0] == "POST" for item in fake.calls),
                                 1 if fail_ack else 0)
                self.assertEqual("UNCONFIRMED" in errors, fail_ack)
                self.assertEqual("request 100 submitted" in output, fail_ack)
                self.assertEqual(run.call_count, 3)
                self.assertEqual(sleep.call_args_list, [call(1), call(2)])


class ReservationReadRetryTests(unittest.TestCase):
    def test_get_retries_each_explicit_transient_http_status(self):
        for status in (502, 503, 504):
            for message in (f"gh: HTTP {status}", f"gh: Server error (HTTP {status})\n"):
                with self.subTest(message=message):
                    failure = subprocess.CompletedProcess([], 1, "", message)
                    success = subprocess.CompletedProcess([], 0, '{"id":7}', "")
                    with patch.object(reserve.subprocess, "run", side_effect=[failure, success]) as run, \
                            patch.object(reserve.time, "sleep") as sleep:
                        self.assertEqual(reserve.api("GET", "user"), {"id": 7})
                    self.assertEqual(run.call_count, 2)
                    self.assertEqual(run.call_args_list[0], run.call_args_list[1])
                    sleep.assert_called_once_with(1)

    def test_fixed_graphql_queries_retry_without_changing_payload(self):
        for query in (reserve.COMMENTS_QUERY, reserve.CLAIM_QUERY, reserve.PR_HEAD_QUERY):
            for message in ("gh: HTTP 504", "gh: Gateway Timeout (HTTP 504)"):
                with self.subTest(query=query.splitlines()[0], message=message):
                    payload = {"query": query, "variables": {"owner": "owner", "name": "repo"}}
                    failure = subprocess.CompletedProcess([], 1, "", message)
                    success = subprocess.CompletedProcess([], 0, '{"data":{}}', "")
                    with patch.object(reserve.subprocess, "run", side_effect=[failure, success]) as run, \
                            patch.object(reserve.time, "sleep") as sleep:
                        self.assertEqual(reserve.api("POST", "graphql", payload), {"data": {}})
                    self.assertEqual(run.call_count, 2)
                    self.assertEqual(run.call_args_list[0], run.call_args_list[1])
                    self.assertEqual(json.loads(run.call_args.kwargs["input"]), payload)
                    sleep.assert_called_once_with(1)

    def test_duplicate_guard_recovers_from_transient_read(self):
        response = {"data": {"repository": {
            "defaultBranchRef": {"name": "main"},
            "object": {"__typename": "Tree", "entries": []},
            "pullRequests": {"nodes": [], "pageInfo": {"hasNextPage": False}}}}}
        failure = subprocess.CompletedProcess([], 1, "", "gh: HTTP 504")
        success = subprocess.CompletedProcess([], 0, json.dumps(response), "")
        with patch.object(reserve.subprocess, "run", side_effect=[failure, success]) as run, \
                patch.object(reserve.time, "sleep") as sleep:
            self.assertEqual(reserve.claim_status(ADDRESS), (0, ""))
        self.assertEqual(run.call_count, 2)
        sleep.assert_called_once_with(1)

    def test_read_timeout_recovers_and_repeated_failures_are_bounded(self):
        for method, endpoint, payload in (
                ("GET", "user", None),
                ("POST", "graphql", {"query": reserve.COMMENTS_QUERY})):
            with self.subTest(method=method):
                timeout = subprocess.TimeoutExpired("gh", 60)
                success = subprocess.CompletedProcess([], 0, '{"ok":true}', "")
                with patch.object(reserve.subprocess, "run", side_effect=[timeout, success]) as run, \
                        patch.object(reserve.time, "sleep") as sleep:
                    self.assertEqual(reserve.api(method, endpoint, payload), {"ok": True})
                self.assertEqual(run.call_count, 2)
                sleep.assert_called_once_with(1)

                for error in (timeout,
                              subprocess.CompletedProcess([], 1, "", "gh: HTTP 504"),
                              subprocess.CompletedProcess(
                                  [], 1, "", "gh: Service Unavailable (HTTP 503)")):
                    with self.subTest(error=error), \
                            patch.object(reserve.subprocess, "run", side_effect=[error] * 3) as run, \
                            patch.object(reserve.time, "sleep") as sleep:
                        with self.assertRaises(reserve.LedgerError):
                            reserve.api(method, endpoint, payload)
                    self.assertEqual(run.call_count, 3)
                    self.assertEqual(sleep.call_args_list, [call(1), call(2)])

    def test_permanent_and_ambiguous_read_failures_do_not_retry(self):
        for message in (
                "gh: Requires authentication (HTTP 401)",
                "gh: Resource not accessible by integration (HTTP 403)",
                f"gh: {reserve.COMMENT_CAPACITY_MESSAGE} (HTTP 403)",
                "gh: Not Found (HTTP 404)",
                "gh: Validation Failed (HTTP 422)",
                "gh: Too Many Requests (HTTP 429)",
                "gh: Internal Server Error (HTTP 500)",
                "connection failed", "response mentioned HTTP 504",
                "gh: HTTP 500", "gh: HTTP 403", "prefix gh: HTTP 504",
                "gh: HTTP 504\nconnection lost",
                "gh: Gateway Timeout (HTTP 504)\nconnection lost"):
            with self.subTest(message=message):
                failure = subprocess.CompletedProcess([], 1, "", message)
                with patch.object(reserve.subprocess, "run", return_value=failure) as run, \
                        patch.object(reserve.time, "sleep") as sleep:
                    with self.assertRaises(reserve.LedgerError):
                        reserve.api("GET", "user")
                run.assert_called_once()
                sleep.assert_not_called()
        with patch.object(reserve.subprocess, "run", side_effect=OSError("missing gh")) as run, \
                patch.object(reserve.time, "sleep") as sleep:
            with self.assertRaises(reserve.LedgerError):
                reserve.api("GET", "user")
        run.assert_called_once()
        sleep.assert_not_called()

    def test_mutations_and_unproven_graphql_requests_never_retry(self):
        requests = [
            ("POST", "repos/owner/repo/issues/66/comments", {"body": "request"}),
            ("PATCH", "repos/owner/repo/issues/66", {"body": "ledger"}),
            ("PUT", "repos/owner/repo/issues/66/lock", {}),
            ("DELETE", "repos/owner/repo/issues/comments/100", None)]
        for method in ("GET", "POST"):
            for payload in (
                    {"query": 'mutation { addComment(input:{body:"query"}) { clientMutationId } }'},
                    {"query": "query { viewer { login } }"},
                    {"query": reserve.CLAIM_QUERY + "\nmutation { deleteIssue(input:{}) { clientMutationId } }"},
                    {"query": reserve.CLAIM_QUERY, "operationName": "unknown"},
                    None):
                requests.append((method, "graphql", payload))
        failure = subprocess.CompletedProcess([], 1, "", "gh: Gateway Timeout (HTTP 504)")
        for method, endpoint, payload in requests:
            for error in (failure, subprocess.CompletedProcess([], 1, "", "gh: HTTP 504"),
                          subprocess.TimeoutExpired("gh", 60)):
                with self.subTest(method=method, endpoint=endpoint, payload=payload, error=error), \
                        patch.object(reserve.subprocess, "run", side_effect=[error]) as run, \
                        patch.object(reserve.time, "sleep") as sleep:
                    with self.assertRaises(reserve.LedgerError):
                        reserve.api(method, endpoint, payload)
                run.assert_called_once()
                sleep.assert_not_called()

    def test_invalid_json_and_graphql_errors_do_not_retry(self):
        with patch.object(reserve.subprocess, "run", return_value=subprocess.CompletedProcess(
                [], 0, "not JSON", "")) as run, patch.object(reserve.time, "sleep") as sleep:
            with self.assertRaises(reserve.LedgerError):
                reserve.api("GET", "user")
        run.assert_called_once()
        sleep.assert_not_called()
        response = json.dumps({"errors": [{"message": "unavailable"}]})
        with patch.object(reserve.subprocess, "run", return_value=subprocess.CompletedProcess(
                [], 0, response, "")) as run, patch.object(reserve.time, "sleep") as sleep:
            with self.assertRaises(reserve.LedgerError):
                reserve.decomp_query(reserve.CLAIM_QUERY)
        run.assert_called_once()
        sleep.assert_not_called()


class FakePRHeadAPI:
    HEAD, ROOT, SOURCE, BLOB = (digit * 40 for digit in "1234")

    def __init__(self, repository=None, present=True):
        self.repository = repository or reserve.DECOMP_REPO
        self.calls = []
        self.pull = {"number": 18, "title": "Recovered functions", "body": "",
                     "state": "OPEN", "headRefOid": self.HEAD,
                     "headRepository": {"nameWithOwner": self.repository}}
        self.current = dict(self.pull)
        self.commit = {"sha": self.HEAD, "tree": {"sha": self.ROOT}}
        self.root = {"sha": self.ROOT, "truncated": False, "tree": [
            {"path": "src", "type": "tree", "mode": "040000", "sha": self.SOURCE}]}
        self.source = {"sha": self.SOURCE, "truncated": False, "tree": [
            {"path": "08136538.c" if present else "08011040.c", "type": "blob",
             "mode": "100644", "sha": self.BLOB}]}
        self.default_entries = []
        self.unavailable = None

    def __call__(self, method, endpoint, payload=None):
        self.calls.append((method, endpoint, payload))
        if endpoint == self.unavailable:
            raise reserve.LedgerError("source snapshot unavailable")
        if (method, endpoint) == ("POST", "graphql"):
            query = payload["query"]
            if query == reserve.CLAIM_QUERY:
                repository = {
                    "defaultBranchRef": {"name": "main"},
                    "object": {"__typename": "Tree", "entries": self.default_entries},
                    "pullRequests": {"nodes": [self.pull],
                                     "pageInfo": {"hasNextPage": False}}}
            elif query == reserve.PR_HEAD_QUERY:
                if payload["variables"]["number"] != 18:
                    raise AssertionError("wrong PR rechecked")
                repository = {"pullRequest": self.current}
            else:
                raise AssertionError("unexpected GraphQL query")
            return {"data": {"repository": repository}}
        prefix = f"repos/{self.repository}/git/"
        objects = {prefix + "commits/" + self.HEAD: self.commit,
                   prefix + "trees/" + self.ROOT: self.root,
                   prefix + "trees/" + self.SOURCE + "?recursive=1": self.source}
        if method == "GET" and endpoint in objects:
            return objects[endpoint]
        raise AssertionError(f"unexpected API call: {method} {endpoint}")


class ReservationPRHeadTests(unittest.TestCase):
    TARGET = "0x08136538"

    def check(self, fake):
        with patch.object(reserve, "api", side_effect=fake):
            return reserve.claim_status(self.TARGET)

    def test_complete_head_source_detected_beyond_capped_changed_files(self):
        fake = FakePRHeadAPI()
        fake.pull["changedFiles"] = 4401
        fake.pull["files"] = {
            "nodes": [{"path": f"docs/match/{i:08X}.md"} for i in range(3000)],
            "pageInfo": {"hasNextPage": False}}
        code, message = self.check(fake)
        self.assertEqual(code, 5)
        self.assertIn("IN PR #18", message)
        self.assertNotIn("files(", reserve.CLAIM_QUERY)
        self.assertEqual(len(fake.calls), 5)
        self.assertEqual(fake.calls[-1][2]["query"], reserve.PR_HEAD_QUERY)

    def test_fork_head_uses_its_pinned_commit_and_source_tree(self):
        fake = FakePRHeadAPI(repository="contributor/fftadecomp")
        self.assertEqual(self.check(fake)[0], 5)
        reads = [endpoint for method, endpoint, _ in fake.calls if method == "GET"]
        self.assertEqual(reads, [
            f"repos/{fake.repository}/git/commits/{fake.HEAD}",
            f"repos/{fake.repository}/git/trees/{fake.ROOT}",
            f"repos/{fake.repository}/git/trees/{fake.SOURCE}?recursive=1"])
        self.assertEqual(fake.calls[-1][2]["variables"]["owner"], reserve.DECOMP_REPO.split("/")[0])

    def test_absent_source_is_free_only_after_head_recheck(self):
        fake = FakePRHeadAPI(present=False)
        self.assertEqual(self.check(fake), (0, ""))
        self.assertEqual(fake.calls[-1][2]["query"], reserve.PR_HEAD_QUERY)

    def test_nested_source_is_detected(self):
        fake = FakePRHeadAPI()
        fake.source["tree"][0]["path"] = "20101/08136538.c"
        self.assertEqual(self.check(fake)[0], 5)

    def test_absent_src_directory_is_valid_only_with_unchanged_head(self):
        fake = FakePRHeadAPI(present=False)
        fake.root["tree"] = []
        self.assertEqual(self.check(fake), (0, ""))
        self.assertEqual(fake.calls[-1][2]["query"], reserve.PR_HEAD_QUERY)
        self.assertEqual(len(fake.calls), 4)

    def test_default_branch_match_precedes_pr_queries(self):
        fake = FakePRHeadAPI()
        fake.default_entries = [{"name": "08136538.c", "type": "blob"}]
        code, message = self.check(fake)
        self.assertEqual(code, 4)
        self.assertIn("MATCHED: src/08136538.c", message)
        self.assertEqual(len(fake.calls), 1)

    def test_title_and_body_guards_precede_tree_lookup(self):
        for field, text in (("title", "Recover func_08136538"),
                            ("body", "Includes 0x08136538.")):
            with self.subTest(field=field):
                fake = FakePRHeadAPI()
                fake.pull[field] = text
                fake.pull["headRepository"] = None
                self.assertEqual(self.check(fake)[0], 5)
                self.assertEqual(len(fake.calls), 1)

    def test_unavailable_commit_root_or_source_fails_closed(self):
        for suffix in ("commits/" + FakePRHeadAPI.HEAD,
                       "trees/" + FakePRHeadAPI.ROOT,
                       "trees/" + FakePRHeadAPI.SOURCE + "?recursive=1"):
            with self.subTest(suffix=suffix):
                fake = FakePRHeadAPI()
                fake.unavailable = f"repos/{fake.repository}/git/{suffix}"
                with self.assertRaisesRegex(reserve.GuardUnavailable, "snapshot unavailable"):
                    self.check(fake)

    def test_malformed_or_truncated_trees_fail_closed(self):
        for location in ("root", "source"):
            for mutation in ("null", "missing_tree", "missing_truncation", "truncated",
                             "wrong_sha", "bad_entry", "duplicate_entry", "bad_mode",
                             "bad_path", "bad_kind", "bad_entry_sha"):
                with self.subTest(location=location, mutation=mutation):
                    fake = FakePRHeadAPI()
                    tree = getattr(fake, location)
                    if mutation == "null":
                        setattr(fake, location, None)
                    elif mutation == "missing_tree":
                        tree.pop("tree")
                    elif mutation == "missing_truncation":
                        tree.pop("truncated")
                    elif mutation == "truncated":
                        tree["truncated"] = True
                    elif mutation == "wrong_sha":
                        tree["sha"] = "5" * 40
                    elif mutation == "bad_entry":
                        tree["tree"] = [None]
                    elif mutation == "duplicate_entry":
                        tree["tree"] *= 2
                    elif mutation == "bad_mode":
                        tree["tree"][0]["mode"] = []
                    elif mutation == "bad_path":
                        tree["tree"][0]["path"] = "../08136538.c"
                    elif mutation == "bad_kind":
                        tree["tree"][0]["type"] = "unknown"
                    else:
                        tree["tree"][0]["sha"] = "not-a-sha"
                    with self.assertRaises(reserve.GuardUnavailable):
                        self.check(fake)

    def test_malformed_commit_and_head_identity_fail_closed(self):
        for mutation in ("missing_commit", "wrong_commit", "missing_tree", "bad_tree_sha",
                         "missing_repository", "invalid_repository", "invalid_head"):
            with self.subTest(mutation=mutation):
                fake = FakePRHeadAPI()
                if mutation == "missing_commit":
                    fake.commit = None
                elif mutation == "wrong_commit":
                    fake.commit["sha"] = "5" * 40
                elif mutation == "missing_tree":
                    fake.commit.pop("tree")
                elif mutation == "bad_tree_sha":
                    fake.commit["tree"]["sha"] = "main"
                elif mutation == "missing_repository":
                    fake.pull["headRepository"] = None
                elif mutation == "invalid_repository":
                    fake.pull["headRepository"] = {"nameWithOwner": "../other/repo"}
                else:
                    fake.pull["headRefOid"] = "main"
                with self.assertRaises(reserve.GuardUnavailable):
                    self.check(fake)

    def test_changed_or_closed_head_never_returns_a_snapshot_result(self):
        for present in (False, True):
            for mutation in ("commit", "repository", "closed", "missing", "number"):
                with self.subTest(present=present, mutation=mutation):
                    fake = FakePRHeadAPI(present=present)
                    if mutation == "commit":
                        fake.current["headRefOid"] = "5" * 40
                    elif mutation == "repository":
                        fake.current["headRepository"] = {"nameWithOwner": "another/fork"}
                    elif mutation == "closed":
                        fake.current["state"] = "CLOSED"
                    elif mutation == "missing":
                        fake.current = None
                    else:
                        fake.current["number"] = 19
                    with self.assertRaises(reserve.GuardUnavailable):
                        self.check(fake)


if __name__ == "__main__":
    unittest.main()
