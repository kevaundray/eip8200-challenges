#!/usr/bin/env python3
"""Integration tests for the RIPEMD-160 artifact snapshot generator."""

from __future__ import annotations

import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parents[2]
GENERATOR = REPOSITORY / "scripts/generate-ripemd160-artifact-snapshots.py"
BEGIN = "  -- BEGIN GENERATED ENTRIES"
END = "  -- END GENERATED ENTRIES"


def snapshot(indices: str = "0, 1, 2", entries: str = "  stale,") -> str:
    return f"""HEADER SENTINEL
def indices : List (Fin 3) :=
[
  {indices}
]

def entries :=
[
{BEGIN}
{entries}
{END}
]
FOOTER SENTINEL
"""


class GeneratorTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.snapshot = self.directory / "ArtifactSnapshots.lean"
        self.bytecode = self.directory / "reference.hex"
        self.bytecode.write_text("60015f01\n", encoding="ascii")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_generator(self, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(GENERATOR),
                "--snapshot-file",
                str(self.snapshot),
                "--bytecode-file",
                str(self.bytecode),
                *arguments,
            ],
            check=False,
            capture_output=True,
            text=True,
        )

    def test_rewrite_preserves_outside_region_mode_and_is_idempotent(self) -> None:
        self.snapshot.write_text(snapshot(), encoding="utf-8")
        self.snapshot.chmod(0o640)

        rewritten = self.run_generator()

        self.assertEqual(rewritten.returncode, 0, rewritten.stderr)
        generated = self.snapshot.read_text(encoding="utf-8")
        self.assertTrue(generated.startswith("HEADER SENTINEL\n"))
        self.assertTrue(generated.endswith("]\nFOOTER SENTINEL\n"))
        self.assertIn("  ⟨0, .push 1 1⟩,", generated)
        self.assertIn("  ⟨2, .push 0 0⟩,", generated)
        self.assertIn("  ⟨3, op 0x01⟩,", generated)
        self.assertEqual(stat.S_IMODE(self.snapshot.stat().st_mode), 0o640)
        before_check = self.snapshot.read_bytes()

        checked = self.run_generator("--check")

        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertEqual(self.snapshot.read_bytes(), before_check)

    def test_rejects_duplicate_or_stray_markers_without_writing(self) -> None:
        reversed_markers = snapshot().replace(BEGIN, "MARKER PLACEHOLDER")
        reversed_markers = reversed_markers.replace(END, BEGIN)
        reversed_markers = reversed_markers.replace("MARKER PLACEHOLDER", END)
        variants = {
            "duplicate begin": snapshot().replace(BEGIN, f"{BEGIN}\n{BEGIN}"),
            "duplicate end": snapshot().replace(END, f"{END}\n{END}"),
            "stray begin": snapshot().replace(
                "HEADER SENTINEL", "HEADER SENTINEL -- BEGIN GENERATED ENTRIES"
            ),
            "stray end": snapshot().replace(
                "FOOTER SENTINEL", "FOOTER SENTINEL -- END GENERATED ENTRIES"
            ),
            "reversed": reversed_markers,
        }
        for label, contents in variants.items():
            with self.subTest(label=label):
                self.snapshot.write_text(contents, encoding="utf-8")
                before = self.snapshot.read_bytes()

                result = self.run_generator()

                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("marker", result.stderr.lower())
                self.assertEqual(self.snapshot.read_bytes(), before)

    def test_rejects_malformed_indices_without_writing(self) -> None:
        for malformed in [
            "0x1",
            "-1",
            "1_0",
            "0, arbitrary2",
            "0 1",
            "0,,1",
        ]:
            with self.subTest(indices=malformed):
                self.snapshot.write_text(snapshot(indices=malformed), encoding="utf-8")
                before = self.snapshot.read_bytes()

                result = self.run_generator()

                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("indices", result.stderr)
                self.assertEqual(self.snapshot.read_bytes(), before)

    def test_comments_in_indices_do_not_contribute_digits(self) -> None:
        indices = "0, -- ignored 99\n  /- ignored 88 /- nested 77 -/ -/ 1, 2"
        self.snapshot.write_text(snapshot(indices=indices), encoding="utf-8")

        result = self.run_generator()

        self.assertEqual(result.returncode, 0, result.stderr)
        generated = self.snapshot.read_text(encoding="utf-8")
        self.assertIn("  ⟨0, .push 1 1⟩,", generated)
        self.assertIn("  ⟨2, .push 0 0⟩,", generated)
        self.assertIn("  ⟨3, op 0x01⟩,", generated)

    def test_invalid_utf8_snapshot_returns_clean_error(self) -> None:
        self.snapshot.write_bytes(b"\xff")
        before = self.snapshot.read_bytes()

        result = self.run_generator()

        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        self.assertEqual(self.snapshot.read_bytes(), before)

    def test_non_ascii_bytecode_returns_clean_error(self) -> None:
        self.snapshot.write_text(snapshot(), encoding="utf-8")
        self.bytecode.write_bytes(b"\xff")
        before = self.snapshot.read_bytes()

        result = self.run_generator()

        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        self.assertEqual(self.snapshot.read_bytes(), before)

    @unittest.skipIf(os.geteuid() == 0, "permission semantics differ for root")
    def test_write_failure_returns_clean_error_without_truncation(self) -> None:
        self.snapshot.write_text(snapshot(), encoding="utf-8")
        before = self.snapshot.read_bytes()
        self.directory.chmod(0o500)
        try:
            result = self.run_generator()
        finally:
            self.directory.chmod(0o700)

        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        self.assertEqual(self.snapshot.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
