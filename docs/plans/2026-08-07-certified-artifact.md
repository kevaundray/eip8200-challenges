# Certified Artifact Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add a kernel-checked cached-PC artifact boundary and prove it reduces structural overhead on a representative RIPEMD direct trace without changing public correctness interfaces.

**Architecture:** `Challenge.EvmProof.CertifiedArtifact` owns an explicit array of `(pc, instruction)` entries plus one validity certificate tying them to exact bytecode and the selected fork. Its executable `run` follows only selected `Fin` indices and returns the final state with exact cost; `run_sound` lifts that result to `GasSteps`. Existing artifact and stepper APIs remain as compatibility layers while one RIPEMD module validates the migration.

**Tech Stack:** Lean 4.31, Lake, pinned `evm-semantics`, `YulEvmCompiler.Instr`, `Challenge.EvmProof.Stepper`, kernel-checked propositions and axiom guards.

### Task 1: Certify exact rows through the public boundary

**Files:**
- Create: `Checks/CertifiedArtifact.lean`
- Create: `Challenge/EvmProof/CertifiedArtifact.lean`

**Step 1: Write the failing boundary test**

Create a tiny three-instruction table and state the desired public API:

```lean
import Challenge.EvmProof.CertifiedArtifact

namespace Checks.CertifiedArtifact

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof

def rows : Array CertifiedArtifact.Entry := #[
  ⟨0, .push 0 0⟩,
  ⟨1, .push 0 0⟩,
  ⟨2, .op .ADD⟩
]

def code : ByteArray := assemble (rows.toList.map (·.instruction))

theorem rows_valid : CertifiedArtifact.Table.Valid .Osaka code rows := by
  decide

def artifact : CertifiedArtifact .Osaka code :=
  CertifiedArtifact.certify rows rows_valid

def staleRows : Array CertifiedArtifact.Entry := rows.set! 1 ⟨7, .push 0 0⟩

example : ¬ CertifiedArtifact.Table.Valid .Osaka code staleRows := by
  decide

end Checks.CertifiedArtifact
```

**Step 2: Run the test to verify RED**

Run: `lake build Checks.CertifiedArtifact`

Expected: FAIL because `Challenge.EvmProof.CertifiedArtifact` does not exist.

**Step 3: Implement the minimal certificate**

Define `Entry`, cumulative `instructionPCs`, `Table.Valid`, and
`CertifiedArtifact.certify`. `Table.Valid` must provide reusable theorems for:

```lean
theorem Valid.assembly_eq : assemble instructions = code
theorem Valid.pc_eq (index : Fin rows.size) :
  rows[index].pc = programArtifact.instructionPC index.val
theorem Valid.wellFormed (index : Fin rows.size) :
  Stepper.WellFormed fork rows[index].instruction
```

Use ordinary `decide`, `rfl`, and structural lemmas only.

**Step 4: Run the test to verify GREEN**

Run: `lake build Checks.CertifiedArtifact`

Expected: PASS.

**Step 5: Commit**

```sh
git add Checks/CertifiedArtifact.lean Challenge/EvmProof/CertifiedArtifact.lean
git commit -m "feat: certify cached bytecode locations"
```

### Task 2: Execute a cached-PC path and return exact cost

**Files:**
- Modify: `Checks/CertifiedArtifact.lean`
- Modify: `Challenge/EvmProof/CertifiedArtifact.lean`

**Step 1: Add one failing execution test**

Using `Challenge.Ripemd160.initialState code #[] 0`, define the expected state
after `PUSH0; PUSH0; ADD` and assert:

```lean
def path : List (Fin artifact.rows.size) := [0, 1, 2]

example : artifact.run path start = some (finish, 8) := by
  rfl
```

The exact expected cost is derived from `Stepper.instrCost`, not duplicated as
an implementation constant; adjust the displayed numeral if the pinned Osaka
cost evaluates differently.

**Step 2: Run the test to verify RED**

Run: `lake build Checks.CertifiedArtifact`

Expected: FAIL because `CertifiedArtifact.run` does not exist.

**Step 3: Implement minimal cached execution**

Add private single-entry execution and public block execution:

```lean
def run (artifact : CertifiedArtifact fork code)
    (path : List (Fin artifact.rows.size)) (state : State) :
    Option (State × Nat)
```

Compare `state.pc.toNat` with the stored `Entry.pc`, call
`Stepper.runInstr`, require intermediate states to remain `.Running`, and sum
`Stepper.instrCost` in execution order. Do not call
`ProgramArtifact.instructionPC` from the evaluator.

**Step 4: Run the test to verify GREEN**

Run: `lake build Checks.CertifiedArtifact`

Expected: PASS.

**Step 5: Commit**

```sh
git add Checks/CertifiedArtifact.lean Challenge/EvmProof/CertifiedArtifact.lean
git commit -m "feat: execute certified cached paths"
```

### Task 3: Lift executable paths to exact-cost semantic traces

**Files:**
- Modify: `Checks/CertifiedArtifact.lean`
- Modify: `Checks/EvmProof.lean`
- Modify: `Challenge/EvmProof/CertifiedArtifact.lean`

**Step 1: Add one failing soundness test**

Package the standard premises in `ExecutionContext` and assert through the
public theorem:

```lean
def context : CertifiedArtifact.ExecutionContext artifact start := {
  code_eq := rfl
  fork_eq := rfl
  running := rfl
  notPrecompile := Challenge.Ripemd160.deployAddress_not_precompile
}

theorem tiny_sound :
    ∃ trace : GasSteps start finish, trace.cost = 8 := by
  obtain ⟨trace, hcost⟩ := artifact.run_sound path run_tiny context
  exact ⟨trace, hcost⟩
```

Add an axiom guard for `tiny_sound` to `Checks/EvmProof.lean` after the theorem
passes, pinning the exact permitted set reported by Lean.

**Step 2: Run the test to verify RED**

Run: `lake build Checks.CertifiedArtifact`

Expected: FAIL because `ExecutionContext` and `run_sound` do not exist.

**Step 3: Implement soundness with current stepper lemmas**

Construct a private `ProgramArtifact` from the certified rows. For each selected
entry, derive `Stepper.Decodes` from `Valid.assembly_eq`, `Valid.pc_eq`, and
`Valid.wellFormed`, then reuse `Stepper.runInstr_sound`. Compose steps exactly
as `Stepper.runLocatedBlock_sound` does and prove the returned `GasSteps.cost`
equals the executable accumulated cost.

**Step 4: Run the tests to verify GREEN**

Run:

```sh
lake build Checks.CertifiedArtifact
lake build Checks.EvmProof
```

Expected: PASS with no warning output.

**Step 5: Commit**

```sh
git add Checks/CertifiedArtifact.lean Checks/EvmProof.lean Challenge/EvmProof/CertifiedArtifact.lean
git commit -m "feat: prove certified path execution sound"
```

### Task 4: Expose the generic boundary without breaking compatibility

**Files:**
- Modify: `Challenge/EvmProof.lean`
- Modify: `Checks.lean`

**Step 1: Add failing umbrella imports**

Import `Checks.CertifiedArtifact` from `Checks.lean` and add a small example in
the test that imports only `Challenge.EvmProof` while referring to
`CertifiedArtifact.Entry`.

**Step 2: Run the test to verify RED**

Run: `lake build Checks`

Expected: FAIL because the new module is not yet exported by the umbrella.

**Step 3: Add the production import**

Add `import Challenge.EvmProof.CertifiedArtifact` to
`Challenge/EvmProof.lean`. Do not alter or delete `ProgramArtifact`,
`Stepper.Located`, or their existing theorems.

**Step 4: Run focused compatibility builds**

Run:

```sh
lake build Challenge.EvmProof
lake build Challenge.Ripemd160.ProofSupport.Bytecode
lake build Checks.CertifiedArtifact
```

Expected: PASS.

**Step 5: Commit**

```sh
git add Challenge/EvmProof.lean Checks.lean Checks/CertifiedArtifact.lean
git commit -m "feat: expose certified artifact proof support"
```

### Task 5: Validate the design on one RIPEMD structural hotspot

**Files:**
- Modify: `Challenge/Ripemd160/Reference/Proofs/Bytecode/Artifact.lean`
- Modify: `Challenge/Ripemd160/Reference/Proofs/Bytecode/Execution.lean`
- Create if useful: `scripts/generate-certified-artifact.sh`

**Step 1: Add a failing RIPEMD adapter theorem**

Define the desired exact-byte certified artifact and rewrite the entry path to
use compact `Fin` indices. Preserve the types and names of
`Execution.gasSteps_entry` and every public downstream theorem.

**Step 2: Run the focused module to verify RED**

Run: `lake build Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution`

Expected: FAIL because the RIPEMD artifact has no certified rows/path yet.

**Step 3: Generate explicit PC snapshots**

Mechanically pair every existing reference instruction with its byte offset,
then define `referenceInstructions` as the projection of those rows. Keep the
existing `referenceArtifact` compatibility value. Prove the cached table valid
with bounded structural lemmas; if a generator is retained, document that its
output is untrusted and kernel-checked.

**Step 4: Migrate only the entry trace**

Replace the fourteen manually certified jump-path blocks in `Execution.lean`
with certified paths and `run_sound`. Avoid changing functional RIPEMD models,
gas schedules, or public correctness statements.

**Step 5: Run focused regression builds**

Run:

```sh
lake build Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution
lake build Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect
```

Expected: PASS.

**Step 6: Commit**

```sh
git add Challenge/Ripemd160/Reference/Proofs/Bytecode/Artifact.lean Challenge/Ripemd160/Reference/Proofs/Bytecode/Execution.lean scripts
git commit -m "refactor: use cached locations for RIPEMD entry trace"
```

### Task 6: Measure and document the result

**Files:**
- Modify: `Challenge/Ripemd160/README.md`
- Modify: `Challenge/Ripemd160/SUBMITTING.md`

**Step 1: Capture reproducible timings**

Measure cold/fresh elaboration of the old commit and feature branch for:

```sh
/usr/bin/time -v lake build Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
/usr/bin/time -v lake build Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution
```

Record wall time and maximum RSS. Run one process at a time to avoid the
parallel-memory distortion found during initial profiling.

**Step 2: Document the contributor workflow**

Explain cached tables, compact paths, the kernel trust boundary, focused build
commands, and when optimized bytecode changes necessarily invalidate proofs.
Do not claim a speedup unless the measurements demonstrate it.

**Step 3: Run final verification**

Run:

```sh
lake build Checks.CertifiedArtifact
lake build Checks.EvmProof
lake build Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect
lake build Challenge.Ripemd160.ProofSupport.Bytecode
git diff --check
```

Expected: all builds and formatting checks pass.

**Step 4: Commit**

```sh
git add Challenge/Ripemd160/README.md Challenge/Ripemd160/SUBMITTING.md
git commit -m "docs: explain cached RIPEMD proof artifacts"
```
