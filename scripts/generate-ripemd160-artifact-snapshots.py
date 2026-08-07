#!/usr/bin/env python3
"""Regenerate the RIPEMD-160 compatibility entries from reference bytecode."""

from __future__ import annotations

import argparse
import difflib
import re
import sys
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


def parse_indices(snapshot: str, path: Path) -> list[int]:
    match = re.search(
        r"def indices\s*:\s*List \(Fin \d+\)\s*:=\s*\[\s*(.*?)\s*\]",
        snapshot,
        flags=re.DOTALL,
    )
    if match is None:
        raise GenerationError(f"cannot find `def indices` in {path}")
    return [int(value) for value in re.findall(r"\d+", match.group(1))]


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
    begin = snapshot.find(BEGIN_MARKER)
    end = snapshot.find(END_MARKER)
    if begin < 0 or end < 0 or end <= begin:
        raise GenerationError(
            f"cannot find ordered generated-entry markers in {path}; "
            "expected `BEGIN GENERATED ENTRIES` and `END GENERATED ENTRIES`"
        )
    content_start = snapshot.find("\n", begin)
    if content_start < 0:
        raise GenerationError(f"begin marker in {path} is not followed by a newline")
    return snapshot[: content_start + 1] + generated + "\n" + snapshot[end:]


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
    except (OSError, GenerationError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

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

    args.snapshot_file.write_text(expected, encoding="utf-8")
    print(f"updated: {args.snapshot_file}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
