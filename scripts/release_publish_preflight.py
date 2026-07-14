#!/usr/bin/env python3
"""Fail closed unless a GitHub release tag is unused (RFC 099)."""
from __future__ import annotations

import json
import os
import sys
import urllib.error
import urllib.request


def decision(status: int, body: str = "") -> tuple[bool, str]:
    if status == 404:
        return True, "release tag is unused"
    if status == 200:
        try:
            assets = [a.get("name", "?") for a in json.loads(body).get("assets", [])]
        except Exception:
            assets = []
        suffix = f"; assets={assets}" if assets else ""
        return False, f"release already exists{suffix}"
    return False, f"GitHub API returned unexpected status {status}"


def self_test() -> int:
    cases = [(404, "", True),
             (200, '{"assets": []}', False),
             (200, '{"assets": [{"name": "henret.tar.gz"}]}', False),
             (500, "", False)]
    errors = sum(decision(status, body)[0] != expected
                 for status, body, expected in cases)
    print(f"release-publish-preflight-selftest: {len(cases)} cases, {errors} error(s)")
    return 1 if errors else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    if len(sys.argv) != 2:
        print("usage: release_publish_preflight.py <tag>", file=sys.stderr)
        return 2
    repo, token = os.environ.get("GITHUB_REPOSITORY"), os.environ.get("GH_TOKEN")
    if not repo or not token:
        print("release-publish-preflight: missing GITHUB_REPOSITORY/GH_TOKEN",
              file=sys.stderr)
        return 1
    url = f"https://api.github.com/repos/{repo}/releases/tags/{sys.argv[1]}"
    req = urllib.request.Request(url, headers={
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "User-Agent": "henret-release-preflight",
        "X-GitHub-Api-Version": "2022-11-28",
    })
    try:
        with urllib.request.urlopen(req, timeout=20) as response:
            status, body = response.status, response.read().decode()
    except urllib.error.HTTPError as error:
        status = error.code
        body = error.read().decode(errors="replace")
    except Exception as error:
        print(f"release-publish-preflight: API request failed: {type(error).__name__}",
              file=sys.stderr)
        return 1
    allowed, reason = decision(status, body)
    print(f"release-publish-preflight: {reason}")
    return 0 if allowed else 1


if __name__ == "__main__":
    raise SystemExit(main())
