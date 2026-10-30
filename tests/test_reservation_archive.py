import base64
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import mock_open, patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import reserve


TIMESTAMP = "2026-10-29T00:00:00Z"
ADDRESS = "0x08011040"


def oid(value):
    return hashlib.sha1(json.dumps(value, sort_keys=True).encode()).hexdigest()


def comment(request_id, request, owner=7):
    return {"id": request_id, "user": {"id": owner, "type": "User"},
            "body": reserve.REQUEST_PREFIX + json.dumps(request, ensure_ascii=False, indent=2),
            "created_at": TIMESTAMP, "updated_at": TIMESTAMP,
            "issue_url": f"https://api.github.com/repos/{reserve.KIT_REPO}/issues/66"}


def pair(claim_id=100, release_id=101, owner=7, address=ADDRESS):
    claim = comment(claim_id, {"operation": "claim", "address": address,
                              "who": "lane", "note": "natural source attempt"}, owner)
    release = comment(release_id, {"operation": "release", "address": address,
                                  "who": "lane", "claim_id": claim_id,
                                  "reason": "Complete natural C misses; retained reason Ω",
                                  "tried": "-mthumb-interwork -O2; genuine field layouts",
                                  "unmatchable": True}, owner)
    state = {"version": 1, "cursor": 0, "rows": [], "results": []}
    for entry in (claim, release):
        state = reserve.apply_comment(state, entry, set(), TIMESTAMP,
                                      claim_check=lambda address: (0, "FREE"))
    state["cursor"] = release_id + 1  # The current cursor itself is never retired.
    return state, [claim, release]


class FakeArchiveAPI:
    def __init__(self, state, comments):
        self.state = copy.deepcopy(state)
        self.comments = {item["id"]: copy.deepcopy(item) for item in comments}
        self.calls, self.deletes = [], []
        self.blobs, self.trees, self.commits = {}, {}, {}
        self.head = None
        self.fail = None
        self.conflict = False
        self.uncertain = False
        self.changed = None
        self.delete_failure = None
        self.deleted_once = False
        self.comment_count = 2500

    def __call__(self, method, endpoint, payload=None):
        self.calls.append((method, endpoint, copy.deepcopy(payload)))
        if self.fail and self.fail(method, endpoint, payload):
            raise reserve.LedgerError("injected archive failure")
        if endpoint == reserve.endpoint():
            if method == "GET":
                return {"number": 66, "state": "open", "body": reserve.render(self.state),
                        "comments": self.comment_count}
            if method == "PATCH":
                self.state = reserve.parse_ledger(payload["body"])
                return {"body": payload["body"]}
        comments = f"repos/{reserve.KIT_REPO}/issues/comments/"
        if endpoint.startswith(comments):
            request_id = int(endpoint.removeprefix(comments))
            if method == "GET":
                if request_id not in self.comments:
                    raise reserve.LedgerError("GitHub request failed: gh: Not Found (HTTP 404)")
                if self.changed and self.head:
                    self.changed(self.comments[request_id])
                return copy.deepcopy(self.comments[request_id])
            if method == "DELETE":
                if self.delete_failure == request_id and not self.deleted_once:
                    self.deleted_once = True
                    raise reserve.LedgerError("interrupted delete")
                if request_id not in self.comments:
                    raise AssertionError("repeated deletion without a read")
                del self.comments[request_id]
                self.comment_count -= 1
                self.deletes.append(request_id)
                return None
        prefix = f"repos/{reserve.KIT_REPO}/git/"
        suffix = endpoint.removeprefix(prefix)
        if method == "GET" and suffix.startswith("matching-refs/"):
            if self.head is None:
                return []
            return [{"ref": reserve.ARCHIVE_REF,
                     "object": {"sha": self.head, "type": "commit"}}]
        if method == "POST" and suffix == "blobs":
            data = payload["content"].encode()
            sha = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            self.blobs[sha] = {"sha": sha, "encoding": "base64",
                               "content": base64.b64encode(data).decode()}
            return {"sha": sha}
        if method == "GET" and suffix.startswith("blobs/"):
            return copy.deepcopy(self.blobs[suffix.split("/")[1]])
        if method == "POST" and suffix == "trees":
            entries = copy.deepcopy(self.trees.get(payload.get("base_tree"), {}))
            entries.update({item["path"]: item for item in payload["tree"]})
            sha = oid(entries)
            self.trees[sha] = entries
            return {"sha": sha}
        if method == "GET" and suffix.startswith("trees/"):
            sha = suffix.split("/")[1].split("?")[0]
            return {"sha": sha, "tree": list(self.trees[sha].values()), "truncated": False}
        if method == "POST" and suffix == "commits":
            sha = oid(payload)
            self.commits[sha] = {"sha": sha, "tree": {"sha": payload["tree"]},
                                  "parents": [{"sha": item, "url": "server-url"} for item in payload["parents"]]}
            if self.conflict and payload["parents"]:
                self.head = "f" * 40
            return {"sha": sha}
        if method == "GET" and suffix.startswith("commits/"):
            return copy.deepcopy(self.commits[suffix.split("/")[1]])
        if method == "POST" and suffix == "refs":
            if self.head:
                raise reserve.LedgerError("ref exists")
            self.head = payload["sha"]
            return {"ref": payload["ref"]}
        if method == "PATCH" and suffix.startswith("refs/"):
            self.assert_ref_update(payload)
            if not self.uncertain:
                self.head = payload["sha"]
            return {"object": {"sha": payload["sha"]}}
        raise AssertionError(f"unexpected API call {method} {endpoint}")

    def assert_ref_update(self, payload):
        if payload["force"] is not False:
            raise AssertionError("forced archive update")
        parents = self.commits[payload["sha"]]["parents"]
        if parents[0]["sha"] != self.head:
            raise reserve.LedgerError("non-fast-forward ref conflict")


class ReservationArchiveTests(unittest.TestCase):
    def setUp(self):
        self.pins = patch.object(reserve, "LEDGER_NUMBER", 66)
        self.pins.start()
        self.addCleanup(self.pins.stop)

    def run_archive(self, fake, bodies=None):
        with patch.object(reserve, "api", side_effect=fake), contextlib.redirect_stdout(io.StringIO()):
            archive = reserve.ReceiptArchive()
            state = copy.deepcopy(fake.state)
            archive.capture(state, bodies)
            archive.retire(state)
            return archive

    def test_full_ledger_bootstraps_legacy_pair_without_posting_comment(self):
        state, comments = pair()
        fake = FakeArchiveAPI(state, comments)
        with patch.object(reserve, "api", side_effect=fake), \
                patch.object(reserve, "comments_after", return_value=[]), \
                patch.object(reserve, "unmatchable", return_value=set()), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(reserve.drain(archive_closed=True), 0)
            archive = reserve.ReceiptArchive()
            closed = archive.read("issues/66/closed/100.json")
        self.assertEqual(fake.deletes, [101, 100])
        self.assertEqual(fake.comment_count, 2498)
        self.assertFalse(any(method == "POST" and endpoint.endswith("/comments")
                             for method, endpoint, payload in fake.calls))
        for key, snapshot in zip(("claim", "release"), comments):
            self.assertEqual(closed[key]["comment"], snapshot)
            self.assertEqual(closed[key]["result"], state["results"][0 if key == "claim" else 1])
            self.assertEqual(closed[key]["body_provenance"], "snapshot-at-archive")
            self.assertEqual(closed[key]["acceptance_body_sha256"], "UNPROVEN")
        release = reserve.parse_request(closed["release"]["comment"]["body"])
        self.assertTrue(release["unmatchable"])
        self.assertEqual(release["reason"], "Complete natural C misses; retained reason Ω")
        self.assertIn("-O2", release["tried"])
        first_delete = next(i for i, item in enumerate(fake.calls) if item[0] == "DELETE")
        self.assertTrue(any(method == "GET" and "/git/blobs/" in endpoint
                            for method, endpoint, payload in fake.calls[:first_delete]))

    def test_future_acceptance_body_survives_expired_recent_claim_result(self):
        state, comments = pair()
        active = reserve.apply_comment({"version": 1, "cursor": 0, "rows": [], "results": []},
                                      comments[0], set(), TIMESTAMP,
                                      claim_check=lambda address: (0, "FREE"))
        fake = FakeArchiveAPI(active, comments)
        self.run_archive(fake, {100: comments[0]["body"]})
        self.assertEqual(fake.deletes, [])
        fake.state = state
        fake.state["results"] = state["results"][1:]
        archive = self.run_archive(fake, {101: comments[1]["body"]})
        with patch.object(reserve, "api", side_effect=fake):
            closed = archive.read("issues/66/closed/100.json")
        self.assertEqual(fake.deletes, [101, 100])
        for key in ("claim", "release"):
            self.assertEqual(closed[key]["body_provenance"], "acceptance-time")
            self.assertEqual(closed[key]["acceptance_body_sha256"], closed[key]["body_sha256"])

    def test_full_rom_closed_pairs_preserve_late_rom_coordinates(self):
        for address in ("0x08150000", "0x08A38A2C", "0x08FFFFFE"):
            with self.subTest(address=address):
                state, comments = pair(address=address)
                fake = FakeArchiveAPI(state, comments)
                archive = self.run_archive(fake)
                with patch.object(reserve, "api", side_effect=fake):
                    closed = archive.read("issues/66/closed/100.json")
                self.assertEqual(fake.deletes, [101, 100])
                for operation, snapshot in zip(("claim", "release"), comments):
                    self.assertEqual(closed[operation]["comment"], snapshot)
                    self.assertEqual(closed[operation]["result"]["address"], address)
                    self.assertEqual(reserve.validate_receipt(closed[operation], operation)["address"], address)

    def test_publication_failures_and_ref_conflicts_delete_nothing(self):
        for failure in ("blob", "tree", "commit", "ref", "readback", "conflict", "uncertain"):
            with self.subTest(failure=failure):
                state, comments = pair()
                fake = FakeArchiveAPI(state, comments)
                if failure == "conflict":
                    fake.conflict = True
                elif failure == "uncertain":
                    fake.uncertain = True
                else:
                    fake.fail = lambda method, endpoint, payload, failure=failure: (
                        (failure == "blob" and method == "POST" and endpoint.endswith("/blobs")) or
                        (failure == "tree" and method == "POST" and endpoint.endswith("/trees") and "base_tree" in payload) or
                        (failure == "commit" and method == "POST" and endpoint.endswith("/commits") and payload["parents"]) or
                        (failure == "ref" and method == "PATCH" and "/git/refs/" in endpoint) or
                        (failure == "readback" and method == "GET" and "/git/blobs/" in endpoint))
                with self.assertRaises(reserve.LedgerError):
                    self.run_archive(fake)
                self.assertEqual(fake.deletes, [])
                self.assertEqual(set(fake.comments), {100, 101})

    def test_unacknowledged_rejected_foreign_and_control_edits_never_delete(self):
        for mutation in ("missing_claim", "missing_release", "rejected", "owner", "lane",
                         "generation", "address", "flag", "issue"):
            with self.subTest(mutation=mutation):
                state, comments = pair()
                if mutation == "missing_claim":
                    state["results"] = state["results"][1:]
                elif mutation == "missing_release":
                    state["results"] = state["results"][:1]
                elif mutation == "rejected":
                    state["results"][1].update(status="rejected", code=1)
                elif mutation == "owner":
                    comments[1]["user"]["id"] = 8
                elif mutation == "issue":
                    comments[1]["issue_url"] += "7"
                else:
                    request = reserve.parse_request(comments[1]["body"])
                    key, value = {"lane": ("who", "other"), "generation": ("claim_id", 99),
                                  "address": ("address", "0x08011044"), "flag": ("unmatchable", False)}[mutation]
                    request[key] = value
                    comments[1]["body"] = reserve.REQUEST_PREFIX + json.dumps(request)
                fake = FakeArchiveAPI(state, comments)
                try:
                    self.run_archive(fake)
                except reserve.LedgerError:
                    pass
                self.assertEqual(fake.deletes, [])

    def test_active_new_generation_and_current_cursor_are_excluded(self):
        for mutation in ("cursor", "active"):
            with self.subTest(mutation=mutation):
                state, comments = pair()
                if mutation == "cursor":
                    state["cursor"] = 101
                else:
                    next_claim = comment(103, {"operation": "claim", "address": ADDRESS,
                                               "who": "next", "note": ""})
                    comments.append(next_claim)
                    state = reserve.apply_comment(state, next_claim, set(), TIMESTAMP,
                                                  claim_check=lambda address: (0, "FREE"))
                fake = FakeArchiveAPI(state, comments)
                self.run_archive(fake)
                self.assertEqual(fake.deletes, [])

    def test_snapshot_edit_after_publication_aborts_deletion(self):
        state, comments = pair()
        fake = FakeArchiveAPI(state, comments)
        # Initialization has a head too; activate the race only once receipts exist.
        def change(snapshot):
            if any("base_tree" in (payload or {}) for method, endpoint, payload in fake.calls):
                snapshot["body"] += " "
        fake.changed = change
        with self.assertRaisesRegex(reserve.LedgerError, "comment changed"):
            self.run_archive(fake)
        self.assertEqual(fake.deletes, [])

    def test_partial_delete_and_completed_retry_are_idempotent(self):
        state, comments = pair()
        fake = FakeArchiveAPI(state, comments)
        fake.delete_failure = 100
        with self.assertRaisesRegex(reserve.LedgerError, "interrupted delete"):
            self.run_archive(fake)
        self.assertEqual(fake.deletes, [101])
        self.run_archive(fake)
        self.assertEqual(fake.deletes, [101, 100])
        self.run_archive(fake)
        self.assertEqual(fake.deletes, [101, 100])

    def test_changed_acceptance_body_is_not_mislabelled_as_original(self):
        state, comments = pair()
        fake = FakeArchiveAPI(state, comments)
        with self.assertRaisesRegex(reserve.LedgerError, "changed after broker acceptance"):
            self.run_archive(fake, {100: comments[0]["body"] + " "})
        self.assertEqual(fake.deletes, [])

    def test_clients_and_untrusted_broker_get_no_archive_authority(self):
        with patch.object(reserve, "trusted_event", side_effect=reserve.LedgerError("untrusted")), \
                patch.object(reserve, "ReceiptArchive") as archive, \
                patch.object(sys, "argv", ["reserve.py", "--no-pull", "broker", "--archive-closed"]), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(reserve.main(), 2)
        archive.assert_not_called()
        state, comments = pair()
        fake = FakeArchiveAPI(state, comments)
        with patch.object(reserve, "api", side_effect=fake), \
                patch.object(reserve, "ReceiptArchive") as archive, \
                patch.object(reserve, "comments_after", return_value=[]), \
                patch.object(reserve, "unmatchable", return_value=set()), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(reserve.drain(), 0)
        archive.assert_not_called()
        self.assertEqual(fake.deletes, [])

    def test_legacy_edited_freeform_body_is_preserved_with_honest_provenance(self):
        state, comments = pair()
        request = reserve.parse_request(comments[1]["body"])
        request["reason"] = "Edited historical explanation; original wording not proved"
        comments[1]["body"] = reserve.REQUEST_PREFIX + json.dumps(request)
        comments[1]["updated_at"] = "2026-10-29T00:01:00Z"
        fake = FakeArchiveAPI(state, comments)
        archive = self.run_archive(fake)
        with patch.object(reserve, "api", side_effect=fake):
            receipt = archive.read("issues/66/closed/100.json")["release"]
        self.assertEqual(receipt["comment"], comments[1])
        self.assertEqual(receipt["acceptance_body_sha256"], "UNPROVEN")
        self.assertEqual(fake.deletes, [101, 100])

    def test_ref_or_ledger_change_during_final_snapshot_checks_deletes_nothing(self):
        for mutation in ("ref", "ledger"):
            with self.subTest(mutation=mutation):
                state, comments = pair()
                fake = FakeArchiveAPI(state, comments)
                def change(snapshot):
                    if any("base_tree" in (payload or {}) for method, endpoint, payload in fake.calls):
                        if mutation == "ref":
                            fake.head = "f" * 40
                        else:
                            fake.state["cursor"] += 1
                fake.changed = change
                with self.assertRaises(reserve.LedgerError):
                    self.run_archive(fake)
                self.assertEqual(fake.deletes, [])

    def test_published_tree_and_blob_must_really_contain_the_archived_bytes(self):
        for mutation in ("tree", "blob", "parents", "truncated"):
            with self.subTest(mutation=mutation):
                state, comments = pair()
                fake = FakeArchiveAPI(state, comments)
                def api(method, endpoint, payload=None):
                    response = fake(method, endpoint, payload)
                    if any("base_tree" in (value or {}) for verb, path, value in fake.calls):
                        if mutation == "tree" and method == "GET" and "/git/trees/" in endpoint:
                            response["tree"] = []
                        elif mutation == "blob" and method == "GET" and "/git/blobs/" in endpoint:
                            response["content"] = base64.b64encode(b"{}").decode()
                        elif mutation == "parents" and method == "GET" and "/git/commits/" in endpoint:
                            response["parents"] = []
                        elif mutation == "truncated" and method == "GET" and "/git/trees/" in endpoint:
                            response["truncated"] = True
                    return response
                with patch.object(reserve, "api", side_effect=api), contextlib.redirect_stdout(io.StringIO()):
                    with self.assertRaises(reserve.LedgerError):
                        archive = reserve.ReceiptArchive()
                        archive.capture(state)
                        archive.retire(state)
                self.assertEqual(fake.deletes, [])

    def test_final_index_write_failure_retries_from_already_durable_pairs(self):
        state, comments = pair()
        fake = FakeArchiveAPI(state, comments)
        fake.fail = lambda method, endpoint, payload: bool(fake.deletes) and method == "PATCH" and "/git/refs/" in endpoint
        with self.assertRaises(reserve.LedgerError):
            self.run_archive(fake)
        self.assertEqual(fake.deletes, [101, 100])
        fake.fail = None
        archive = self.run_archive(fake)
        self.assertEqual(archive.index["generations"], [])
        self.assertEqual(fake.deletes, [101, 100])

    def test_large_drain_checkpoints_before_the_64_result_window_can_expire(self):
        initial = {"version": 1, "cursor": 0, "rows": [], "results": []}
        comments = []
        for claim_id in range(100, 180, 2):
            _, generation = pair(claim_id, claim_id + 1)
            comments.extend(generation)
        fake = FakeArchiveAPI(initial, comments)
        with patch.object(reserve, "api", side_effect=fake), \
                patch.object(reserve, "comments_after", side_effect=lambda cursor: [
                    copy.deepcopy(item) for item in fake.comments.values() if item["id"] > cursor]), \
                patch.object(reserve, "claim_status", return_value=(0, "FREE")), \
                patch.object(reserve, "unmatchable", return_value=set()), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(reserve.drain(archive_closed=True), 0)
            archive = reserve.ReceiptArchive()
            first = archive.read("issues/66/closed/100.json")
            last = archive.read("issues/66/closed/178.json")
        self.assertEqual(len(fake.state["results"]), 64)
        self.assertEqual(len(fake.deletes), 78)
        self.assertEqual(set(fake.comments), {178, 179})
        for generation in (first, last):
            for operation in ("claim", "release"):
                self.assertEqual(generation[operation]["body_provenance"], "acceptance-time")

    def test_only_default_branch_trusted_scheduled_or_manual_events_can_archive(self):
        event = {"repository": {"full_name": reserve.KIT_REPO, "default_branch": "main"}}
        environment = {"GITHUB_ACTIONS": "true", "GITHUB_REPOSITORY": reserve.KIT_REPO,
                       "GITHUB_REF": "refs/heads/main", "GITHUB_EVENT_NAME": "schedule",
                       "GITHUB_EVENT_PATH": "fixture-event.json"}
        for event_name in ("schedule", "workflow_dispatch"):
            with self.subTest(event=event_name), \
                    patch.dict(reserve.os.environ, dict(environment, GITHUB_EVENT_NAME=event_name), clear=True), \
                    patch("builtins.open", mock_open(read_data=json.dumps(event))), \
                    patch.object(reserve, "_resolve_ledger_number", return_value=66):
                self.assertEqual(reserve.trusted_event(), reserve.STALE_DAYS)
        for key, value in (("GITHUB_ACTIONS", "false"), ("GITHUB_REPOSITORY", "foreign/repo"),
                           ("GITHUB_REF", "refs/heads/untrusted"), ("GITHUB_EVENT_NAME", "pull_request")):
            with self.subTest(key=key), \
                    patch.dict(reserve.os.environ, dict(environment, **{key: value}), clear=True), \
                    patch("builtins.open", mock_open(read_data=json.dumps(event))), \
                    patch.object(reserve, "_resolve_ledger_number", return_value=66):
                with self.assertRaises(reserve.LedgerError):
                    reserve.trusted_event()
        workflow = (Path(__file__).resolve().parents[1] / ".github/workflows/reservations.yml").read_text()
        self.assertIn("group: ffta-address-ledger-50", workflow)
        self.assertIn("cancel-in-progress: false", workflow)
        self.assertIn("contents: write", workflow)
        self.assertIn("broker --archive-closed", workflow)
        self.assertIn("github.event.repository.default_branch", workflow)
        self.assertIn("schedule:", workflow)

    def test_delete_204_is_empty_success_and_404_is_read_only_missing(self):
        with patch.object(reserve.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")):
            self.assertIsNone(reserve.api("DELETE", "repos/owner/repo/issues/comments/100"))
        with patch.object(reserve.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "", "gh: Not Found (HTTP 404)")) as run, \
                patch.object(reserve.time, "sleep") as sleep:
            self.assertIsNone(reserve.receipt_comment(100))
            run.assert_called_once()
            sleep.assert_not_called()
        with patch.object(reserve.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "", "gh: Not Found (HTTP 404)")) as run, \
                patch.object(reserve.time, "sleep") as sleep:
            with self.assertRaises(reserve.LedgerError):
                reserve.api("DELETE", "repos/owner/repo/issues/comments/100")
            run.assert_called_once()
            sleep.assert_not_called()

    def test_comment_snapshot_read_retries_transient_error_before_confirmed_404(self):
        transient = subprocess.CompletedProcess([], 1, "", "gh: Service Unavailable (HTTP 503)")
        missing = subprocess.CompletedProcess([], 1, "", "gh: Not Found (HTTP 404)")
        with patch.object(reserve.subprocess, "run", side_effect=[transient, missing]) as run, \
                patch.object(reserve.time, "sleep") as sleep:
            self.assertIsNone(reserve.receipt_comment(100))
        self.assertEqual(run.call_count, 2)
        self.assertEqual(run.call_args_list[0], run.call_args_list[1])
        sleep.assert_called_once_with(1)


if __name__ == "__main__":
    unittest.main()
