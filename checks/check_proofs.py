#!/usr/bin/env python3
"""Scan proof sources and audit transitive axiom dependencies.

Run after `lake build`. The script uses Python's standard library and Lean's
declaration environment to check every project declaration's axiom dependencies.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys


FORBIDDEN = re.compile(r"(?<![\w'?!])(?:sorry|admit|sorryAx|axiom|unsafe|native_decide)(?![\w'?!])")
RAW_STRING = re.compile(r'r(#+)?"')
CHAR_LITERAL = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^\\'\n])'")


def mask_noncode(source: str) -> str:
    """Blank noncode and ordinary quoted identifiers, preserving line positions.

    Lean block comments nest. Strings may contain escapes or use raw delimiters.
    Interpolated strings are left visible so their embedded proof terms are scanned.
    """
    masked = list(source)
    index = 0
    size = len(source)

    def blank(start: int, end: int) -> None:
        for position in range(start, end):
            if source[position] != "\n":
                masked[position] = " "

    while index < size:
        start = index
        if source.startswith("--", index):
            end = source.find("\n", index)
            index = size if end < 0 else end
        elif source.startswith("/-", index):
            depth = 1
            index += 2
            while index < size and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError("unterminated block comment")
        elif source[index] == "«":
            end = source.find("»", index + 1)
            if end < 0:
                raise ValueError("unterminated quoted identifier")
            # Quoting a constant's name does not change which constant Lean uses.
            # Other quoted identifiers may legitimately contain keyword text.
            if source[index + 1 : end] == "sorryAx":
                index = end + 1
                continue
            index = end + 1
        elif (match := CHAR_LITERAL.match(source, index)) is not None and (
            index == 0 or not (source[index - 1].isalnum() or source[index - 1] in "_'?")
        ):
            index = match.end()
        elif (match := RAW_STRING.match(source, index)) is not None and (
            index == 0 or not (source[index - 1].isalnum() or source[index - 1] == "_")
        ):
            delimiter = '"' + (match.group(1) or "")
            end = source.find(delimiter, match.end())
            if end < 0:
                raise ValueError("unterminated raw string")
            index = end + len(delimiter)
        elif source[index] == '"':
            # Do not conceal Lean terms inside interpolated strings such as s!"{...}".
            interpolated = index >= 2 and source[index - 1] == "!"
            index += 1
            while index < size:
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise ValueError("unterminated string")
            if interpolated:
                continue
        else:
            index += 1
            continue
        blank(start, index)
    return "".join(masked)


def lean_sources(root: Path):
    """Walk project sources without descending into dependencies or Git metadata."""
    for directory, subdirs, files in os.walk(root):
        subdirs[:] = sorted(name for name in subdirs if name not in {".lake", ".git"})
        for name in sorted(files):
            if name.endswith(".lean"):
                yield Path(directory) / name


def scan_sources(root: Path) -> tuple[int, list[str]]:
    failures: list[str] = []
    count = 0
    for path in lean_sources(root):
        count += 1
        source = path.read_text(encoding="utf-8")
        try:
            code = mask_noncode(source)
        except ValueError as error:
            failures.append(f"{path.relative_to(root)}: {error}")
            continue
        for match in FORBIDDEN.finditer(code):
            line = source.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(root)}:{line}: forbidden token {match.group()!r}")
    return count, failures


def check_library_imports(root: Path) -> list[str]:
    """Require the aggregate to import every library module for the Lean audit."""
    aggregate = root / "QuantumBackflow.lean"
    if not aggregate.is_file():
        return ["Missing QuantumBackflow.lean aggregate"]
    imports = set(re.findall(r"^import\s+(\S+)\s*$", mask_noncode(
        aggregate.read_text(encoding="utf-8")), re.MULTILINE))
    expected = {
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / "QuantumBackflow").rglob("*.lean")
    }
    return [f"Library module missing from aggregate: {name}"
            for name in sorted(expected - imports)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=os.environ.get("LAKE", "lake"), help="Lake executable")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    count, failures = scan_sources(root)
    failures.extend(check_library_imports(root))
    if failures:
        print("Proof source scan failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(f"Source scan passed ({count} Lean files; dependencies excluded).", flush=True)
    try:
        result = subprocess.run(
            [args.lake, "env", "lean", "checks/Axioms.lean"], cwd=root, check=False
        )
    except OSError as error:
        print(f"Could not run the Lean audit: {error}", file=sys.stderr)
        return 1
    if result.returncode:
        print("Lean dependency audit failed. Run `lake build` first if imports are missing.", file=sys.stderr)
        return result.returncode
    print("Proof integrity audit passed: all project declarations use only permitted standard axioms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
