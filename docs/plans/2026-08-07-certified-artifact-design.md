# Certified Artifact Design

## Goal

Make direct EVM proofs for optimized precompile replacements elaborate in
proportion to the selected instruction block, rather than repeatedly reducing
the complete bytecode artifact prefix. The public challenge endpoints remain
`DirectProof bytecode` and `Correct bytecode`.

## Problem

`ProgramArtifact.instructionPC index` computes the length of the assembled
instruction prefix. RIPEMD-160 proof modules repeatedly construct `Located`
values and normalize that function for high instruction indices. In an
invalidated build, `Artifact.lean` exceeded 90 seconds and 5.5 GB RSS;
individual trace modules later reached approximately 13 GB RSS.

BLAKE2f's `Fin`-indexed `locatedPath` improves source ergonomics, but its
locations still compute PCs from full instruction prefixes. The optimization
must therefore cache PCs as certified data, not only shorten path syntax.

## Scalable public workflow

For a large concrete byte array, start from the bytecode rather than writing a
whole row table by hand:

```lean
def bytecodeCertificate :
    CertifiedArtifact.BytecodeCertificate fork code := by
  decide

def artifact : CertifiedArtifact fork code :=
  CertifiedArtifact.fromBytecode bytecodeCertificate
```

`fromBytecode` disassembles once, derives cached `(pc, instruction)` rows, and
uses the linear `BytecodeCertificate` to prove exact reassembly and fork
well-formedness. Generated data remains untrusted: a bad chunk or instruction
boundary makes the certificate fail.

Next discharge each artifact lookup near the artifact definition. A
`DecoderCertificate` mentions only stable bytecode, fork, and one explicit
entry; `SelectedEntry` packages that entry with its compact certificate:

```lean
theorem siteDecoder :
    CertifiedArtifact.DecoderCertificate fork code entry :=
  artifact.decoderCertificate index entry rowAtIndex

def site : CertifiedArtifact.SelectedEntry fork code :=
  ⟨entry, siteDecoder⟩
```

Build short `List (SelectedEntry fork code)` segments and evaluate them with
`runSelected`. Prove each bounded segment with the explicit
`runSelected_nil`/`runSelected_cons` equations; these equations expose one
step without unfolding the private evaluator or the complete artifact table.
Compose already-proved segments with `runSelected_append`, then seal semantic
soundness through the proposition-valued theorem:

```lean
theorem segmentResult :
    artifact.runSelected segment start = some (finish, cost) := by
  simp only [CertifiedArtifact.runSelected_cons,
    CertifiedArtifact.runSelected_nil]

theorem pathResult :
    artifact.runSelected (left ++ right) start =
      some (finish, leftCost + rightCost) :=
  artifact.runSelected_append left right leftResult midRunning rightResult

theorem pathSound :
    ∃ trace : GasSteps start finish, trace.cost = cost :=
  artifact.runSelected_sound_exists path pathResult context
```

`runSelected` uses the explicit cached PCs and returns the exact accumulated
gas cost. `runSelected_sound_exists` hides decoder installation, stable
execution-context propagation, and semantic trace composition behind an
opaque proposition-valued boundary. `runSelected_sound` is also available
when a caller needs the trace value directly, but the existential boundary is
usually cheaper for a large concrete path.

The earlier `run : List (Fin artifact.rows.size) → ...` and `run_sound` API is
retained for compatibility and small abstract artifacts. It is unsuitable for
large concrete artifacts: resolving `artifact.rows[index]` in downstream proof
terms can normalize the complete derived table and recreate the elaboration
spike that this design avoids. New large-artifact proofs should use
`DecoderCertificate`, `SelectedEntry`, and `runSelected`.

The implementation uses ordinary structures and theorems. It adds no
`native_decide`, project axiom, or source-level `opaque` declaration.

## Data flow

```text
submitted bytecode + linear BytecodeCertificate
        │
        ▼
fromBytecode ──► kernel-checked cached rows and exact assembly equality
        │
        ▼
decoderCertificate ──► compact SelectedEntry sites
        │
        ▼
runSelected segments ── runSelected_append ──► final state + exact cost
        │
        ▼
runSelected_sound_exists ──► ∃ exact-cost GasSteps trace
        │
        ▼
RIPEMD phase refinement ──► DirectProof ──► unchanged Correct
```

Generation is untrusted convenience tooling: bad bytes, PCs, instruction
boundaries, or fork facts make `BytecodeCertificate` or the derived
`Table.Valid` proof fail. Large paths are evaluated in bounded public segments
while preserving this boundary.

## Compatibility and migration

The existing `ProgramArtifact`, `Stepper.Located`, and `runLocatedBlock` APIs
remain available. The first migration targets one RIPEMD trace module and
keeps all public reference theorem names unchanged. Other challenges can adopt
the new boundary independently.

After this work, a separate refactor will move the reusable RIPEMD word,
padding, compression, block-absorption, and output refinements into
`Challenge.Ripemd160.ProofSupport`.

## Verification

Boundary tests use tiny real bytecodes and only the public interface:

- `fromBytecode` certifies structurally derived rows against exact bytes;
- stale PCs and mismatched bytes are rejected;
- a `SelectedEntry` path returns the expected state and exact cost;
- explicit evaluator equations and `runSelected_append` compose bounded paths;
- `runSelected_sound_exists` returns a `GasSteps` proof with that same cost;
- axiom checks reject `native_decide`, `sorry`, and new axioms.

The RIPEMD migration is accepted only after its focused theorem build passes
and before/after wall-time and peak-RSS measurements show whether cached PCs
remove the structural normalization spike.
