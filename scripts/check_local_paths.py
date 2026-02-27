#!/usr/bin/env python3
"""Reject machine-local absolute paths in tracked text files."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

PATTERNS = (
    re.compile(r"(?<![\w/])[A-Za-z]:[\\/][A-Za-z0-9._~\-\\/]+"),
    re.compile(r"(?<![\w/])/mnt/[A-Za-z]/[A-Za-z0-9._~\-/]+"),
    re.compile(r"(?<![\w/])/home/[A-Za-z0-9._-]+/[A-Za-z0-9._~\-/]+"),
    re.compile(r"(?<![\w/])/Users/[A-Za-z0-9._-]+/[A-Za-z0-9._~\-/]+"),
)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def git_list_files(root: Path, staged: bool) -> list[Path]:
    if staged:
        cmd = ["git", "diff", "--cached", "--name-only", "--diff-filter=ACMR", "-z"]
    else:
        cmd = ["git", "ls-files", "-z"]
    out = subprocess.check_output(cmd, cwd=root)
    rels = [p for p in out.decode("utf-8", errors="replace").split("\0") if p]
    return [root / rel for rel in rels]


def is_binary(data: bytes) -> bool:
    return b"\x00" in data


def scan_file(path: Path, root: Path) -> list[tuple[int, str]]:
    if not path.exists() or not path.is_file():
        return []
    data = path.read_bytes()
    if is_binary(data):
        return []
    text = data.decode("utf-8", errors="replace")
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        for pat in PATTERNS:
            m = pat.search(line)
            if m:
                hits.append((lineno, m.group(0)))
                break
    return hits


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--staged", action="store_true", help="scan staged files only")
    args = ap.parse_args()

    root = repo_root()
    try:
        files = git_list_files(root, args.staged)
    except subprocess.CalledProcessError as exc:
        print(f"path hygiene check failed to list files: {exc}", file=sys.stderr)
        return 2

    findings: list[tuple[Path, int, str]] = []
    for path in files:
        for lineno, match in scan_file(path, root):
            findings.append((path, lineno, match))

    if findings:
        print("Machine-local absolute path(s) found:")
        for path, lineno, match in findings:
            rel = path.relative_to(root)
            print(f"  {rel}:{lineno}: {match}")
        print(
            "\nUse env vars or relative paths; do not commit workstation-specific absolute paths."
        )
        return 1

    print("Path hygiene check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
