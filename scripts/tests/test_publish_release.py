"""Regression tests for publication gates and create-only GitHub operations."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch
from urllib.parse import urlsplit


SCRIPTS = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("publish_release", SCRIPTS / "publish_release.py")
assert SPEC is not None and SPEC.loader is not None
publication = importlib.util.module_from_spec(SPEC)
with patch.object(sys, "path", [str(SCRIPTS), *sys.path]):
    SPEC.loader.exec_module(publication)

# Synthetic release data: independent of the real repository's versions and tags.
REPOSITORY = "dxogrp/morew"
SHA = "a" * 40
TAG = "v1.2.3"
SECRET = "publication-test-secret"
ROOT = Path("/release-checkout")
ENVIRONMENT = {
    "GITHUB_REPOSITORY": REPOSITORY,
    "VERIFIED_SHA": SHA,
    "RELEASE_TAG": TAG,
    "GH_TOKEN": SECRET,
}
VERIFIED = {
    "package_version": "1.2.3",
    "release_tag": TAG,
    "source_sha": SHA,
    "lean_toolchain": "leanprover/lean4:v4.33.0",
    "verification_run_url": f"https://github.com/{REPOSITORY}/actions/runs/123",
}


def tag_response(**changes):
    result = {"ref": f"refs/tags/{TAG}", "object": {"type": "commit", "sha": SHA}}
    result.update(changes)
    return result


def release_response(**changes):
    result = {
        "tag_name": TAG,
        "draft": False,
        "prerelease": False,
        "html_url": f"https://github.com/{REPOSITORY}/releases/tag/{TAG}",
    }
    result.update(changes)
    return result


class PublicationTests(unittest.TestCase):
    def setUp(self):
        environment = patch.dict(os.environ, ENVIRONMENT, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        verification = patch.object(publication, "verify", return_value=dict(VERIFIED))
        self.verify = verification.start()
        self.addCleanup(verification.stop)
        unused_release = patch.object(publication, "require_unused_release")
        self.unused_release = unused_release.start()
        self.addCleanup(unused_release.stop)
        posting = patch.object(publication, "api_post")
        self.post = posting.start()
        self.addCleanup(posting.stop)
        self.post.side_effect = [tag_response(), release_response()]

    def test_creates_pinned_tag_before_publishing_stable_release(self):
        result = publication.publish(ROOT)
        self.assertEqual(result, f"https://github.com/{REPOSITORY}/releases/tag/{TAG}")
        self.assertEqual([request.args[:2] for request in self.post.call_args_list], [
            (REPOSITORY, "git/refs"), (REPOSITORY, "releases"),
        ])
        tag_payload, release_payload = [request.args[2] for request in self.post.call_args_list]
        self.assertEqual(tag_payload["ref"], f"refs/tags/{TAG}")
        self.assertEqual(tag_payload["sha"], SHA)
        self.assertEqual(release_payload["tag_name"], TAG)
        self.assertEqual(release_payload["target_commitish"], SHA)
        self.assertIs(release_payload["draft"], False)
        self.assertIs(release_payload["prerelease"], False)
        self.assertIs(release_payload["generate_release_notes"], True)

    def test_failed_reverification_prevents_all_writes(self):
        self.verify.side_effect = publication.VerificationError("CI is no longer successful")
        with self.assertRaises(publication.VerificationError):
            publication.publish(ROOT)
        self.post.assert_not_called()

    def test_missing_expected_identity_prevents_all_writes(self):
        for variable in ("VERIFIED_SHA", "RELEASE_TAG", "GITHUB_REPOSITORY"):
            with self.subTest(variable=variable), patch.dict(os.environ, {variable: ""}):
                with self.assertRaises(publication.VerificationError):
                    publication.publish(ROOT)
                self.post.assert_not_called()

    def test_changed_verified_identity_prevents_all_writes(self):
        for change in ({"source_sha": "b" * 40}, {"release_tag": "v1.2.4"}):
            with self.subTest(change=change):
                self.verify.return_value = {**VERIFIED, **change}
                with self.assertRaises(publication.VerificationError):
                    publication.publish(ROOT)
                self.post.assert_not_called()

    def test_failed_release_lookup_prevents_tag_reservation(self):
        self.unused_release.side_effect = publication.VerificationError("Cannot read releases")
        with self.assertRaises(publication.VerificationError):
            publication.publish(ROOT)
        self.post.assert_not_called()

    def test_tag_conflict_prevents_release_creation(self):
        self.post.side_effect = publication.VerificationError("Tag already exists")
        with self.assertRaises(publication.VerificationError):
            publication.publish(ROOT)
        self.assertEqual([request.args[1] for request in self.post.call_args_list], ["git/refs"])

    def test_unconfirmed_tag_identity_prevents_release_creation(self):
        responses = [
            {},
            tag_response(ref="refs/tags/v1.2.4"),
            tag_response(object=None),
            tag_response(object="not an object"),
            tag_response(object={}),
            tag_response(object={"type": "tag", "sha": SHA}),
            tag_response(object={"type": "commit", "sha": "b" * 40}),
        ]
        for response in responses:
            with self.subTest(response=response):
                self.post.reset_mock()
                self.post.side_effect = [response, release_response()]
                with self.assertRaises(publication.VerificationError):
                    publication.publish(ROOT)
                self.assertEqual(self.post.call_count, 1)
                self.assertEqual(self.post.call_args.args[1], "git/refs")

    def test_failed_release_creation_retains_reserved_tag(self):
        self.post.side_effect = [
            tag_response(), publication.VerificationError("Publication request failed")
        ]
        with self.assertRaises(publication.VerificationError):
            publication.publish(ROOT)
        self.assertEqual([request.args[1] for request in self.post.call_args_list], [
            "git/refs", "releases"
        ])

    def test_unconfirmed_release_response_does_not_claim_success_or_retry(self):
        responses = [
            {},
            release_response(tag_name="v1.2.4"),
            release_response(draft=True),
            release_response(prerelease=True),
            release_response(draft=0),
            release_response(prerelease=None),
        ]
        for response in responses:
            with self.subTest(response=response):
                self.post.reset_mock()
                self.post.side_effect = [tag_response(), response]
                with self.assertRaises(publication.VerificationError):
                    publication.publish(ROOT)
                self.assertEqual([request.args[1] for request in self.post.call_args_list], [
                    "git/refs", "releases"
                ])

    def test_returns_canonical_url_instead_of_trusting_response_url(self):
        self.post.side_effect = [
            tag_response(), release_response(html_url="https://unrelated.example/release")
        ]
        self.assertEqual(
            publication.publish(ROOT), f"https://github.com/{REPOSITORY}/releases/tag/{TAG}"
        )


class ApiPostTests(unittest.TestCase):
    def setUp(self):
        environment = patch.dict(os.environ, ENVIRONMENT, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        process = patch.object(publication.subprocess, "run")
        self.run = process.start()
        self.addCleanup(process.stop)

    def test_posts_json_to_exact_repository_without_token_argument(self):
        response = tag_response()
        self.run.return_value = subprocess.CompletedProcess([], 0, json.dumps(response), "")
        payload = {"ref": f"refs/tags/{TAG}", "sha": SHA}
        self.assertEqual(publication.api_post(REPOSITORY, "git/refs", payload), response)
        self.run.assert_called_once()
        command = self.run.call_args.args[0]
        self.assertEqual(command[0:2], ["gh", "api"])
        self.assertIn(f"/repos/{REPOSITORY}/git/refs", command)
        self.assertEqual(command[command.index("--method") + 1], "POST")
        self.assertEqual(command[command.index("--input") + 1], "-")
        self.assertNotIn(SECRET, " ".join(command))
        self.assertEqual(json.loads(self.run.call_args.kwargs["input"]), payload)
        self.assertGreater(self.run.call_args.kwargs["timeout"], 0)

    def test_missing_token_does_not_start_process(self):
        with patch.dict(os.environ, {"GH_TOKEN": ""}):
            with self.assertRaises(publication.VerificationError):
                publication.api_post(REPOSITORY, "git/refs", {})
        self.run.assert_not_called()

    def test_api_failure_does_not_expose_process_output(self):
        self.run.return_value = subprocess.CompletedProcess([], 1, SECRET, SECRET)
        with self.assertRaises(publication.VerificationError) as raised:
            publication.api_post(REPOSITORY, "git/refs", {})
        self.assertNotIn(SECRET, str(raised.exception))

    def test_malformed_api_response_fails_without_leaking_output(self):
        for response in (SECRET, "null", "[]", json.dumps(SECRET)):
            with self.subTest(response=response):
                self.run.return_value = subprocess.CompletedProcess([], 0, response, SECRET)
                with self.assertRaises(publication.VerificationError) as raised:
                    publication.api_post(REPOSITORY, "git/refs", {})
                self.assertNotIn(SECRET, str(raised.exception))

    def test_process_errors_and_timeouts_are_redacted(self):
        errors = [
            OSError(SECRET),
            subprocess.TimeoutExpired(["gh", SECRET], 120, output=SECRET, stderr=SECRET),
        ]
        for error in errors:
            with self.subTest(error=type(error).__name__):
                self.run.side_effect = error
                with self.assertRaises(publication.VerificationError) as raised:
                    publication.api_post(REPOSITORY, "git/refs", {})
                self.assertNotIn(SECRET, str(raised.exception))


class ExistingReleaseTests(unittest.TestCase):
    def setUp(self):
        environment = patch.dict(os.environ, ENVIRONMENT, clear=True)
        environment.start()
        self.addCleanup(environment.stop)
        process = patch.object(publication.subprocess, "run")
        self.run = process.start()
        self.addCleanup(process.stop)

    def test_existing_published_or_draft_release_prevents_all_writes(self):
        for draft in (False, True):
            with self.subTest(draft=draft):
                self.run.return_value = subprocess.CompletedProcess(
                    [], 0, json.dumps([[{"tag_name": TAG, "draft": draft}]]), ""
                )
                with patch.object(publication, "verify", return_value=dict(VERIFIED)):
                    with patch.object(publication, "api_post") as post:
                        with self.assertRaises(publication.VerificationError):
                            publication.publish(ROOT)
                        post.assert_not_called()

    def test_unrelated_releases_on_paginated_response_are_allowed(self):
        pages = [[{"tag_name": "v1.2.2", "draft": False}], [{"tag_name": "v2.0.0", "draft": True}]]
        self.run.return_value = subprocess.CompletedProcess([], 0, json.dumps(pages), "")
        publication.require_unused_release(REPOSITORY, TAG)
        command = self.run.call_args.args[0]
        self.assertIn(f"/repos/{REPOSITORY}/releases", [urlsplit(argument).path for argument in command])
        self.assertIn("--paginate", command)
        self.assertIn("--slurp", command)
        self.assertEqual(command[command.index("--method") + 1], "GET")

    def test_matching_release_on_later_page_is_rejected(self):
        pages = [[{"tag_name": "v1.0.0"}], [{"tag_name": TAG, "draft": True}]]
        self.run.return_value = subprocess.CompletedProcess([], 0, json.dumps(pages), "")
        with self.assertRaises(publication.VerificationError):
            publication.require_unused_release(REPOSITORY, TAG)

    def test_malformed_listing_fails_closed_without_leaking_output(self):
        for response in (SECRET, "{}", "null", "[{}]", "[[null]]", "[[{}]]"):
            with self.subTest(response=response):
                self.run.return_value = subprocess.CompletedProcess([], 0, response, SECRET)
                with self.assertRaises(publication.VerificationError) as raised:
                    publication.require_unused_release(REPOSITORY, TAG)
                self.assertNotIn(SECRET, str(raised.exception))

    def test_read_failure_or_timeout_is_redacted(self):
        self.run.return_value = subprocess.CompletedProcess([], 1, SECRET, SECRET)
        with self.assertRaises(publication.VerificationError) as raised:
            publication.require_unused_release(REPOSITORY, TAG)
        self.assertNotIn(SECRET, str(raised.exception))
        self.run.side_effect = subprocess.TimeoutExpired(["gh", SECRET], 120, output=SECRET)
        with self.assertRaises(publication.VerificationError) as raised:
            publication.require_unused_release(REPOSITORY, TAG)
        self.assertNotIn(SECRET, str(raised.exception))


if __name__ == "__main__":
    unittest.main()
