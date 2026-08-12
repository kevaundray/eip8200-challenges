#!/usr/bin/env python3
"""Self-test the artifact-first BLS shared/G2ADD cache namespaces."""

from __future__ import annotations

import hashlib
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
WORKFLOW = REPO_ROOT / ".github/workflows/ci.yml"
ARTIFACT_DIRECTORY = REPO_ROOT / "Challenge/Bls12381/Reference/Artifacts"


def artifact_digest(contents: list[tuple[Path, bytes]]) -> str:
    digest = hashlib.sha256()
    for path, content in contents:
        digest.update(path.name.encode())
        digest.update(b"\0")
        digest.update(content)
    return digest.hexdigest()


def shared_prefix(artifact_hash: str) -> str:
    return f"project-shared-v4-linux-x64-dependency-package-{artifact_hash}"


def main() -> None:
    workflow = WORKFLOW.read_text(encoding="utf-8")
    required_fragments = (
        "SHARED_ARTIFACT_HASH: ${{ hashFiles('Challenge/Bls12381/Reference/Artifacts/*.hex') }}",
        'shared_prefix="project-shared-v4-${{ runner.os }}-${{ runner.arch }}-'
        '${DEPENDENCY_HASH}-${PACKAGE_TARGET_HASH}-${SHARED_ARTIFACT_HASH}"',
        'shared_key="${shared_prefix}-${SHARED_SOURCE_HASH}"',
        'echo "shared-restore-prefix=${shared_prefix}-" >> "$GITHUB_OUTPUT"',
        "${{ steps.cache-keys.outputs.shared-restore-prefix }}",
    )
    for fragment in required_fragments:
        if fragment not in workflow:
            raise AssertionError(f"missing cache contract fragment: {fragment}")
    if workflow.index("${SHARED_ARTIFACT_HASH}") > workflow.index("${SHARED_SOURCE_HASH}"):
        raise AssertionError("shared artifact hash must precede shared source hash")
    restore_step = workflow.split("- name: Cache shared project build", 1)[1].split(
        "- name: Set up Lean", 1
    )[0]
    if restore_step.count("steps.cache-keys.outputs.shared-restore-prefix") != 1:
        raise AssertionError("shared build must have exactly one safe restore prefix")
    for legacy in ("project-shared-v3-", "project-shared-v2-", "project-shared-v1-"):
        if legacy in restore_step:
            raise AssertionError(f"unsafe legacy restore prefix remains: {legacy}")

    artifacts = sorted(ARTIFACT_DIRECTORY.glob("*.hex"))
    if len(artifacts) != 7:
        raise AssertionError(f"expected 7 shared BLS artifacts, found {len(artifacts)}")
    original = [(path, path.read_bytes()) for path in artifacts]
    mutated = original.copy()
    index = artifacts.index(ARTIFACT_DIRECTORY / "g2add.hex")
    path, content = mutated[index]
    mutated[index] = (path, content + b"00")

    before = shared_prefix(artifact_digest(original))
    after = shared_prefix(artifact_digest(mutated))
    if before == after:
        raise AssertionError("g2add.hex mutation did not invalidate shared restore prefix")

    g2_before = f"project-bls12381-g2add-v1-linux-x64-{before}-source-artifact"
    g2_after = f"project-bls12381-g2add-v1-linux-x64-{after}-source-artifact"
    if g2_before == g2_after:
        raise AssertionError("g2add.hex mutation did not invalidate derived G2ADD prefix")

    print(
        "BLS cache-policy self-test: PASS "
        "(g2add.hex invalidates shared restore and derived G2ADD prefixes)"
    )


if __name__ == "__main__":
    main()
