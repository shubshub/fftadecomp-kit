import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

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


if __name__ == "__main__":
    unittest.main()
