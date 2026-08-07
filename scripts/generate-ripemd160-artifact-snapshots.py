#!/usr/bin/env python3
"""Regenerate the RIPEMD-160 compatibility entries from reference bytecode."""

from __future__ import annotations

import argparse
import difflib
import os
import re
import stat
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parents[1]
DEFAULT_SNAPSHOT = (
    REPOSITORY
    / "Challenge/Ripemd160/Reference/Proofs/Bytecode/ArtifactSnapshots.lean"
)
DEFAULT_BYTECODE = REPOSITORY / "Challenge/Ripemd160/Reference/reference.hex"
BEGIN_MARKER = "  -- BEGIN GENERATED ENTRIES"
END_MARKER = "  -- END GENERATED ENTRIES"
BEGIN_LABEL = "BEGIN GENERATED ENTRIES"
END_LABEL = "END GENERATED ENTRIES"


class GenerationError(Exception):
    """A malformed input prevented deterministic snapshot generation."""


@dataclass(frozen=True)
class Instruction:
    pc: int
    opcode: int
    push_width: int | None
    push_value: int | None


def parse_bytecode(path: Path) -> bytes:
    try:
        encoded = "".join(path.read_text(encoding="ascii").split())
    except OSError as error:
        raise GenerationError(f"cannot read bytecode {path}: {error}") from error
    if encoded.startswith(("0x", "0X")):
        encoded = encoded[2:]
    try:
        return bytes.fromhex(encoded)
    except ValueError as error:
        raise GenerationError(f"invalid hex in {path}: {error}") from error


def disassemble(bytecode: bytes) -> list[Instruction]:
    instructions: list[Instruction] = []
    pc = 0
    while pc < len(bytecode):
        opcode = bytecode[pc]
        if opcode == 0x5F:
            instructions.append(Instruction(pc, opcode, 0, 0))
            pc += 1
        elif 0x60 <= opcode <= 0x7F:
            width = opcode - 0x5F
            end = pc + 1 + width
            if end > len(bytecode):
                raise GenerationError(
                    f"truncated PUSH{width} at byte {pc}: "
                    f"needs {width} immediate bytes, has {len(bytecode) - pc - 1}"
                )
            value = int.from_bytes(bytecode[pc + 1 : end], "big")
            instructions.append(Instruction(pc, opcode, width, value))
            pc = end
        else:
            instructions.append(Instruction(pc, opcode, None, None))
            pc += 1
    return instructions


def strip_lean_comments(source: str, path: Path) -> str:
    """Replace nested block and line comments with whitespace."""
    stripped: list[str] = []
    index = 0
    block_depth = 0
    while index < len(source):
        if block_depth > 0:
            if source.startswith("/-", index):
                stripped.extend("  ")
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                stripped.extend("  ")
                block_depth -= 1
                index += 2
            else:
                character = source[index]
                stripped.append(character if character in "\r\n" else " ")
                index += 1
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end < 0:
                stripped.extend(" " * (len(source) - index))
                index = len(source)
            else:
                stripped.extend(" " * (end - index))
                index = end
        elif source.startswith("/-", index):
            stripped.extend("  ")
            block_depth = 1
            index += 2
        else:
            stripped.append(source[index])
            index += 1
    if block_depth != 0:
        raise GenerationError(f"unterminated Lean block comment in {path}")
    return "".join(stripped)


def parse_indices(snapshot: str, path: Path) -> list[int]:
    uncommented = strip_lean_comments(snapshot, path)
    header = re.compile(
        r"\bdef\s+indices\s*:\s*List\s*\(\s*Fin\s+[0-9]+\s*\)\s*:=\s*\["
    )
    matches = list(header.finditer(uncommented))
    if len(matches) != 1:
        raise GenerationError(
            f"expected exactly one supported `def indices` declaration in {path}"
        )
    body_start = matches[0].end()
    body_end = uncommented.find("]", body_start)
    if body_end < 0:
        raise GenerationError(f"unterminated `def indices` list in {path}")
    body = uncommented[body_start:body_end]
    grammar = r"\s*(?:[0-9]+(?:\s*,\s*[0-9]+)*\s*,?)?\s*"
    if re.fullmatch(grammar, body) is None:
        raise GenerationError(
            f"unsupported indices syntax in {path}; "
            "expected decimal literals separated by commas"
        )
    return [int(value) for value in re.findall(r"[0-9]+", body)]


def format_entry(instruction: Instruction) -> str:
    if instruction.push_width is None:
        syntax = f"op 0x{instruction.opcode:02x}"
    else:
        syntax = f".push {instruction.push_width} {instruction.push_value}"
    return f"  ⟨{instruction.pc}, {syntax}⟩,"


def generated_region(snapshot: str, snapshot_path: Path, bytecode_path: Path) -> str:
    instructions = disassemble(parse_bytecode(bytecode_path))
    indices = parse_indices(snapshot, snapshot_path)
    entries: list[str] = []
    for index in indices:
        if index >= len(instructions):
            raise GenerationError(
                f"instruction index {index} is outside the {len(instructions)} decoded instructions"
            )
        entries.append(format_entry(instructions[index]))
    return "\n".join(entries)


def replace_region(snapshot: str, generated: str, path: Path) -> str:
    lines = snapshot.splitlines(keepends=True)
    bare_lines = [line.rstrip("\r\n") for line in lines]
    begin_lines = [
        index for index, line in enumerate(bare_lines) if line == BEGIN_MARKER
    ]
    end_lines = [index for index, line in enumerate(bare_lines) if line == END_MARKER]
    begin_mentions = [line for line in bare_lines if BEGIN_LABEL in line]
    end_mentions = [line for line in bare_lines if END_LABEL in line]
    if (
        len(begin_lines) != 1
        or len(end_lines) != 1
        or len(begin_mentions) != 1
        or len(end_mentions) != 1
    ):
        raise GenerationError(
            f"expected exactly one exact standalone begin and end marker in {path}"
        )
    begin = begin_lines[0]
    end = end_lines[0]
    if end <= begin:
        raise GenerationError(f"generated-entry markers are out of order in {path}")
    begin_line = lines[begin]
    if begin_line.endswith("\r\n"):
        newline = "\r\n"
    elif begin_line.endswith("\n"):
        newline = "\n"
    else:
        raise GenerationError(f"begin marker in {path} is not a standalone line")
    region = generated.replace("\n", newline)
    if region:
        region += newline
    return "".join(lines[: begin + 1]) + region + "".join(lines[end:])


def atomic_write(path: Path, contents: str) -> None:
    mode = stat.S_IMODE(path.stat().st_mode)
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            newline="",
            dir=path.parent,
            prefix=f".{path.name}.",
            suffix=".tmp",
            delete=False,
        ) as temporary:
            temporary_path = Path(temporary.name)
            temporary.write(contents)
            temporary.flush()
            os.fchmod(temporary.fileno(), mode)
            os.fsync(temporary.fileno())
        os.replace(temporary_path, path)
        temporary_path = None
    except Exception:
        if temporary_path is not None:
            try:
                temporary_path.unlink(missing_ok=True)
            except OSError:
                pass
        raise


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail without writing if the generated entries are stale",
    )
    parser.add_argument(
        "--snapshot-file",
        type=Path,
        default=DEFAULT_SNAPSHOT,
        help="snapshot file to check or rewrite (useful for isolated tests)",
    )
    parser.add_argument(
        "--bytecode-file",
        type=Path,
        default=DEFAULT_BYTECODE,
        help="hex bytecode input (defaults to the RIPEMD-160 reference)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        original = args.snapshot_file.read_text(encoding="utf-8")
        expected = replace_region(
            original,
            generated_region(original, args.snapshot_file, args.bytecode_file),
            args.snapshot_file,
        )
        if original == expected:
            print(f"up to date: {args.snapshot_file}")
            return 0
        if args.check:
            print(f"stale generated entries: {args.snapshot_file}", file=sys.stderr)
            sys.stderr.writelines(
                difflib.unified_diff(
                    original.splitlines(keepends=True),
                    expected.splitlines(keepends=True),
                    fromfile=str(args.snapshot_file),
                    tofile=f"{args.snapshot_file} (generated)",
                )
            )
            return 1
        atomic_write(args.snapshot_file, expected)
        print(f"updated: {args.snapshot_file}")
        return 0
    except (OSError, UnicodeError, GenerationError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
