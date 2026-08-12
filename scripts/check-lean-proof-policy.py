#!/usr/bin/env python3
"""Reject forbidden proof mechanisms in Lean source files."""

from __future__ import annotations

import re
import sys
from pathlib import Path


FORBIDDEN_WORDS = ("sorry", "admit", "native_decide", "CertifiedArtifact")
IDENTIFIER_EDGE = r"A-Za-z0-9_'"


def mask_comments_and_strings(source: str) -> str:
    """Replace Lean comments and string contents with spaces, preserving lines."""
    result = list(source)
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(source):
        pair = source[index : index + 2]

        if in_line_comment:
            if source[index] == "\n":
                in_line_comment = False
            else:
                result[index] = " "
            index += 1
            continue

        if block_depth:
            if pair == "/-":
                result[index] = result[index + 1] = " "
                block_depth += 1
                index += 2
            elif pair == "-/":
                result[index] = result[index + 1] = " "
                block_depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    result[index] = " "
                index += 1
            continue

        if in_string:
            if source[index] != "\n":
                result[index] = " "
            if escaped:
                escaped = False
            elif source[index] == "\\":
                escaped = True
            elif source[index] == '"':
                in_string = False
            index += 1
            continue

        if pair == "--":
            result[index] = result[index + 1] = " "
            in_line_comment = True
            index += 2
        elif pair == "/-":
            result[index] = result[index + 1] = " "
            block_depth = 1
            index += 2
        elif source[index] == '"':
            result[index] = " "
            in_string = True
            index += 1
        else:
            index += 1

    return "".join(result)


def violations(source: str) -> list[tuple[int, str]]:
    masked = mask_comments_and_strings(source)
    findings: list[tuple[int, str]] = []

    for word in FORBIDDEN_WORDS:
        pattern = re.compile(
            rf"(?<![{IDENTIFIER_EDGE}]){re.escape(word)}(?![{IDENTIFIER_EDGE}])"
        )
        for match in pattern.finditer(masked):
            line = masked.count("\n", 0, match.start()) + 1
            findings.append((line, f"forbidden proof mechanism: {word}"))

    axiom_pattern = re.compile(rf"(?<![{IDENTIFIER_EDGE}])axiom(?![{IDENTIFIER_EDGE}])")
    for match in axiom_pattern.finditer(masked):
        line = masked.count("\n", 0, match.start()) + 1
        findings.append((line, "forbidden axiom declaration"))

    heartbeat_pattern = re.compile(
        rf"(?<![{IDENTIFIER_EDGE}])set_option(?![{IDENTIFIER_EDGE}])"
        rf"\s+maxHeartbeats\s+0(?![0-9])"
    )
    for match in heartbeat_pattern.finditer(masked):
        line = masked.count("\n", 0, match.start()) + 1
        findings.append((line, "forbidden unlimited maxHeartbeats setting"))

    return sorted(findings)


def lean_files(arguments: list[str]) -> list[Path]:
    files: set[Path] = set()
    for argument in arguments:
        path = Path(argument)
        if path.is_dir():
            files.update(candidate for candidate in path.rglob("*.lean") if candidate.is_file())
        elif path.is_file() and path.suffix == ".lean":
            files.add(path)
        else:
            raise ValueError(f"not a Lean file or directory: {argument}")
    return sorted(files)


def main() -> int:
    if len(sys.argv) < 2:
        print(f"usage: {Path(sys.argv[0]).name} PATH [PATH ...]", file=sys.stderr)
        return 2

    try:
        files = lean_files(sys.argv[1:])
    except ValueError as error:
        print(error, file=sys.stderr)
        return 2

    rejected = False
    for path in files:
        for line, message in violations(path.read_text(encoding="utf-8")):
            print(f"{path}:{line}: {message}", file=sys.stderr)
            rejected = True
    return 1 if rejected else 0


if __name__ == "__main__":
    raise SystemExit(main())
