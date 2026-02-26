#!/usr/bin/env python3
import pathlib
import re
import sys


PATTERN = re.compile(r"\b(?:Admitted|Axiom)\b")


def main() -> int:
    root = pathlib.Path(".")
    hits = []
    for path in sorted(root.rglob("*.v")):
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError as exc:
            print(f"proof hygiene FAILED: could not read {path}: {exc}")
            return 1
        for lineno, line in enumerate(lines, start=1):
            if PATTERN.search(line):
                hits.append((path.as_posix(), lineno, line.rstrip()))

    if hits:
        print("proof hygiene FAILED: found Admitted/Axiom.")
        for path, lineno, line in hits:
            print(f"{path}:{lineno}:{line}")
        return 1

    print("proof hygiene OK: no Admitted/Axiom in project .v files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
