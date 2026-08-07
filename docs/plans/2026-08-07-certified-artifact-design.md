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

## Boundary

The challenge-independent module exposes three operations:

```lean
structure Entry where
  pc : Nat
  instruction : YulEvmCompiler.Instr

structure CertifiedArtifact (fork : Fork) (code : ByteArray) where
  rows : Array Entry
  valid : Table.Valid fork code rows

def certify (rows) (valid : Table.Valid fork code rows) :
    CertifiedArtifact fork code

def run (artifact) (path : List (Fin artifact.rows.size)) (state : State) :
    Option (State × Nat)

theorem run_sound
    (hresult : artifact.run path state = some (finalState, cost))
    (context : ExecutionContext artifact state) :
    { trace : GasSteps state finalState // trace.cost = cost }
```

`Table.Valid` binds the rows to exact bytes, proves each stored PC is the
cumulative encoded length, and certifies instruction well-formedness for the
chosen fork. `run` uses stored PCs directly and accumulates exact gas cost.
`run_sound` hides decoder installation, fork checks, environment preservation,
and semantic trace composition.

The implementation uses ordinary structures and theorems. It adds no
`native_decide`, project axiom, or source-level `opaque` declaration.

## Data flow

```text
generated (pc, instruction) rows
        │
        ▼
kernel-checked Table.Valid ── exact assembly equality ──► submitted bytecode
        │
        ▼
CertifiedArtifact.run path state ──► final state + exact cost
        │
        ▼
CertifiedArtifact.run_sound ──► GasSteps
        │
        ▼
RIPEMD phase refinement ──► DirectProof ──► unchanged Correct
```

Generation is untrusted convenience tooling: bad bytes, PCs, instruction
boundaries, or fork facts make `Table.Valid` unprovable. Large generated tables
may be validated in bounded internal chunks while preserving this boundary.

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

- valid rows certify their exact bytes;
- stale PCs and mismatched bytes are rejected;
- a selected path returns the expected state and exact cost;
- `run_sound` returns a `GasSteps` proof with that same cost;
- axiom checks reject `native_decide`, `sorry`, and new axioms.

The RIPEMD migration is accepted only after its focused theorem build passes
and before/after wall-time and peak-RSS measurements show whether cached PCs
remove the structural normalization spike.
