"""Check documentation CI prerequisites or the generated site."""

from __future__ import annotations

import argparse
from html.parser import HTMLParser
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urljoin, urlsplit

from verify_release import (
    VerificationError,
    fetch_workflow_runs,
    latest_successful_run,
    required_environment,
    resolve_commit,
)


SITE_URL = "https://dxogrp.github.io/morew/"
SOURCE_URL = "https://github.com/dxogrp/morew/"
MAX_SITE_BYTES = 1_000_000_000


def check_ci(root: Path) -> dict[str, str]:
    repository = required_environment("GITHUB_REPOSITORY")
    if re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) is None:
        raise VerificationError("GITHUB_REPOSITORY must have the form owner/repository.")
    if required_environment("GITHUB_EVENT_NAME") != "workflow_dispatch":
        raise VerificationError("Documentation deployment requires a workflow_dispatch event.")
    if required_environment("GITHUB_REF") != "refs/heads/main":
        raise VerificationError("Documentation deployment must be dispatched from refs/heads/main.")
    sha = resolve_commit(root, "HEAD")
    if sha != required_environment("GITHUB_SHA"):
        raise VerificationError("The documentation checkout must match GITHUB_SHA exactly.")
    runs = fetch_workflow_runs(repository, "ci.yml", sha, "push")
    url = latest_successful_run(runs, repository, "ci.yml", sha, "push")
    return {"source_sha": sha, "verification_run_url": url}


class Page(HTMLParser):
    def __init__(self, path: Path):
        super().__init__(convert_charrefs=True)
        self.path = path
        self.base: str | None = None
        self.links: list[tuple[str, str]] = []
        self.ids: set[str] = set()

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        for name, value in attrs:
            if name not in {"href", "src"} or value is None:
                continue
            if urlsplit(value).scheme in {"file", "vscode", "vscode-insiders"}:
                raise VerificationError(f"Local source URL in {self.path}: {value}")
            if tag != "base":
                self.links.append((name, value))
        if tag == "base" and self.base is None:
            self.base = attributes.get("href")
        if attributes.get("id"):
            self.ids.add(attributes["id"])


def site_files(site_dir: Path) -> tuple[list[Path], int]:
    if site_dir.is_symlink():
        raise VerificationError(f"Symbolic link in documentation: {site_dir}")
    if not site_dir.is_dir():
        raise VerificationError(f"Documentation directory is missing: {site_dir}")
    files = []
    size = 0
    for directory, subdirs, names in os.walk(site_dir):
        for name in sorted(subdirs + names):
            path = Path(directory) / name
            if path.is_symlink():
                raise VerificationError(f"Symbolic link in documentation: {path}")
        for name in sorted(names):
            path = Path(directory) / name
            size += path.stat().st_size
            files.append(path.relative_to(site_dir))
    if size > MAX_SITE_BYTES:
        raise VerificationError(f"Documentation size {size:,} bytes exceeds {MAX_SITE_BYTES:,} bytes")
    return sorted(files), size


def local_target(value: str, base_url: str, site_dir: Path) -> tuple[Path, str] | None:
    url = urljoin(base_url, value)
    parsed = urlsplit(url)
    base = urlsplit(SITE_URL)
    if (parsed.scheme, parsed.netloc) != (base.scheme, base.netloc):
        return None
    if not parsed.path.startswith(base.path):
        if urlsplit(value).netloc:
            return None
        raise VerificationError(f"Link leaves the {base.path} site: {url}")
    target = site_dir / unquote(parsed.path[len(base.path):])
    if not target.resolve().is_relative_to(site_dir.resolve()):
        raise VerificationError(f"Link leaves the documentation directory: {url}")
    if target.is_dir():
        target /= "index.html"
    return target.relative_to(site_dir), unquote(parsed.fragment)


def check_source_link(url: str, root: Path, source_sha: str) -> bool:
    if not url.startswith(SOURCE_URL):
        return False
    parsed = urlsplit(url)
    parts = unquote(parsed.path).split("/")
    if len(parts) < 5 or parts[3] not in {"blob", "tree"}:
        return False
    if parts[4] != source_sha:
        raise VerificationError(f"Incorrect source commit: {url}")
    source = root.joinpath(*parts[5:])
    if not source.resolve().is_relative_to(root.resolve()) or not source.exists():
        raise VerificationError(f"Source path does not exist: {url}")
    return parts[3] == "blob"


def check_site(root: Path, site_dir: Path, source_sha: str) -> int:
    files, size = site_files(site_dir)
    for index in (Path("index.html"), Path("api/index.html")):
        if index not in files:
            raise VerificationError(f"Missing documentation page: {index}")

    pages = {}
    api_sources = 0
    for path in files:
        if path.suffix != ".html":
            continue
        page = Page(path)
        page.feed((site_dir / path).read_text(encoding="utf-8"))
        page.close()
        sources = sum(
            check_source_link(urljoin(SITE_URL, value), root, source_sha)
            for _, value in page.links
        )
        if path.parts[0] != "api" or sources:
            pages[path] = page
        if path.parts[0] == "api":
            api_sources += sources
    if api_sources == 0:
        raise VerificationError("No Morew API source links were found")

    anchors = []
    for path, page in pages.items():
        page_url = urljoin(SITE_URL, path.as_posix())
        base_url = urljoin(page_url, page.base) if page.base else page_url
        if local_target(base_url, SITE_URL, site_dir) is None:
            raise VerificationError(f"External base URL in {path}: {page.base}")
        for attribute, value in page.links:
            target = local_target(value, base_url, site_dir)
            if target is None:
                continue
            destination, fragment = target
            if not (site_dir / destination).is_file():
                raise VerificationError(f"Missing link target in {path}: {value}")
            if (path.parts[0] != "api" and attribute == "href" and fragment
                and destination.parts[0] == "api" and destination.suffix == ".html"):
                anchors.append((path, destination, fragment))

    for origin, destination, fragment in anchors:
        if destination not in pages:
            page = Page(destination)
            page.feed((site_dir / destination).read_text(encoding="utf-8"))
            pages[destination] = page
        if fragment not in pages[destination].ids:
            raise VerificationError(f"Missing API anchor from {origin}: {destination}#{fragment}")
    return size


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("ci", "site"))
    args = parser.parse_args(argv)
    try:
        root = Path.cwd()
        if args.check == "ci":
            result = check_ci(root)
            message = (
                f"Documentation prerequisites verified for {result['source_sha']}.\n\n"
                f"[Successful CI run]({result['verification_run_url']})"
            )
            if output := os.environ.get("GITHUB_OUTPUT"):
                with Path(output).open("a", encoding="utf-8") as destination:
                    for key, value in result.items():
                        destination.write(f"{key}={value}\n")
        else:
            sha = resolve_commit(root, "HEAD")
            size = check_site(root, root / "build/docs", sha)
            message = f"Documentation checked for {sha}: {size:,} bytes."
        print(message)
        if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
            with Path(summary).open("a", encoding="utf-8") as output:
                output.write(message + "\n")
    except (VerificationError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Documentation check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
