#!/usr/bin/env python3
"""Reject forbidden proof mechanisms in Lean source files."""

from __future__ import annotations

import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path


FORBIDDEN_IDENTIFIERS = {
    "sorry",
    "sorryAx",
    "admit",
    "native_decide",
    "CertifiedArtifact",
}


def mask_comments_and_string_text(source: str) -> str:
    """Mask comments/string text but retain code in interpolated expressions."""
    result = ["\n" if character == "\n" else " " for character in source]

    def skip_line_comment(index: int) -> int:
        while index < len(source) and source[index] != "\n":
            index += 1
        return index

    def skip_block_comment(index: int) -> int:
        depth = 1
        index += 2
        while index < len(source) and depth:
            pair = source[index : index + 2]
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
        return index

    def skip_plain_string(index: int) -> int:
        index += 1
        escaped = False
        while index < len(source):
            character = source[index]
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                return index + 1
            index += 1
        return index

    def scan_interpolated_string(index: int) -> int:
        index += 1
        escaped = False
        while index < len(source):
            character = source[index]
            if escaped:
                escaped = False
                index += 1
            elif character == "\\":
                escaped = True
                index += 1
            elif character == '"':
                return index + 1
            elif character == "{":
                index = scan_code(index + 1, stop_at_closing_brace=True)
            else:
                index += 1
        return index

    def scan_code(index: int, *, stop_at_closing_brace: bool = False) -> int:
        while index < len(source):
            pair = source[index : index + 2]
            character = source[index]
            if pair == "--":
                index = skip_line_comment(index)
            elif pair == "/-":
                index = skip_block_comment(index)
            elif character == '"':
                interpolated = index >= 2 and source[index - 2 : index] == "s!"
                if interpolated:
                    index = scan_interpolated_string(index)
                else:
                    index = skip_plain_string(index)
            elif stop_at_closing_brace and character == "}":
                return index + 1
            elif stop_at_closing_brace and character == "{":
                result[index] = character
                index = scan_code(index + 1, stop_at_closing_brace=True)
            else:
                result[index] = character
                index += 1
        return index

    scan_code(0)
    return "".join(result)


def is_identifier_start(character: str) -> bool:
    if character == "_" or character.isalpha():
        return True
    return unicodedata.category(character).startswith(("L", "M"))


def is_identifier_continue(character: str) -> bool:
    if character in "_'" or character.isalnum():
        return True
    return unicodedata.category(character).startswith(("L", "M", "N"))


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    kind: str


def tokens(masked: str) -> list[Token]:
    result: list[Token] = []
    index = 0
    while index < len(masked):
        character = masked[index]
        if character.isspace():
            index += 1
        elif is_identifier_start(character):
            end = index + 1
            while end < len(masked) and is_identifier_continue(masked[end]):
                end += 1
            result.append(Token(masked[index:end], index, "identifier"))
            index = end
        elif character.isdecimal():
            end = index
            base = 10
            valid_digits = "0123456789_"
            if masked[index : index + 2].lower() == "0x":
                base = 16
                valid_digits = "0123456789abcdefABCDEF_"
                end = index + 2
            elif masked[index : index + 2].lower() == "0b":
                base = 2
                valid_digits = "01_"
                end = index + 2
            elif masked[index : index + 2].lower() == "0o":
                base = 8
                valid_digits = "01234567_"
                end = index + 2
            while end < len(masked) and masked[end] in valid_digits:
                end += 1
            result.append(Token(masked[index:end], index, f"nat:{base}"))
            index = end
        else:
            result.append(Token(character, index, "symbol"))
            index += 1
    return result


def nat_value(token: Token) -> int | None:
    if not token.kind.startswith("nat:"):
        return None
    base = int(token.kind.removeprefix("nat:"))
    spelling = token.text.replace("_", "")
    if base != 10:
        spelling = spelling[2:]
    if not spelling:
        return None
    return int(spelling, base)


def violations(source: str) -> list[tuple[int, str]]:
    masked = mask_comments_and_string_text(source)
    lexed = tokens(masked)
    findings: list[tuple[int, str]] = []

    def add(token: Token, message: str) -> None:
        line = masked.count("\n", 0, token.start) + 1
        findings.append((line, message))

    for token in lexed:
        if token.kind == "identifier" and token.text in FORBIDDEN_IDENTIFIERS:
            add(token, f"forbidden proof mechanism: {token.text}")
        if token.kind == "identifier" and token.text == "axiom":
            add(token, "forbidden axiom declaration")

    for index in range(len(lexed) - 2):
        option, name, value = lexed[index : index + 3]
        if option.text == "set_option" and name.text == "maxHeartbeats":
            if nat_value(value) == 0:
                add(option, "forbidden unlimited maxHeartbeats setting")

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
