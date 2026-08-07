import Challenge.EvmProof.Stepper

set_option warningAsError true

/-!
# Certified cached bytecode locations

`CertifiedArtifact` binds cached instruction locations to exact submitted bytes
and to the opcode rules of a selected fork.  The cache is proof-carrying: every
stored program counter is checked against the cumulative encoded instruction
length, so later execution support can use the stored value directly.
-/

namespace Challenge.EvmProof

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

namespace CertifiedArtifact

/-- One cached instruction boundary. -/
structure Entry where
  pc : Nat
  instruction : Instr

/-- Instructions represented by a table, in table order. -/
def instructions (rows : Array Entry) : List Instr :=
  rows.toList.map (·.instruction)

/-- Byte offset of an instruction index, computed from the encoded prefix. -/
def instructionPC (rows : Array Entry) (index : Nat) : Nat :=
  (assembleBytes ((instructions rows).take index)).length

private def instructionPCsFrom (pc : Nat) : List Entry → List Nat
  | [] => []
  | row :: rest =>
      pc :: instructionPCsFrom (pc + row.instruction.bytes.length) rest

/-- All cumulative instruction offsets, computed in one table traversal. -/
def instructionPCs (rows : Array Entry) : List Nat :=
  instructionPCsFrom 0 rows.toList

private theorem instructionPCsFrom_getElem? (pc : Nat) (rows : List Entry)
    (index : Nat) (hindex : index < rows.length) :
    (instructionPCsFrom pc rows)[index]? = some
      (pc + (assembleBytes ((rows.map (·.instruction)).take index)).length) := by
  induction rows generalizing pc index with
  | nil => simp at hindex
  | cons row rest ih =>
      cases index with
      | zero => simp [instructionPCsFrom]
      | succ index =>
          have hrest : index < rest.length := by simpa using hindex
          simp only [instructionPCsFrom, List.getElem?_cons_succ]
          rw [ih (pc + row.instruction.bytes.length) index hrest]
          simp [assembleBytes_cons, Nat.add_assoc]

namespace Table

private def plainOperation : Operation → Bool
  | .Push _ | .DupN _ | .SwapN _ | .Exchange _ => false
  | _ => true

private theorem plainOperation_valid (operation : Operation)
    (valid : plainOperation operation = true) :
    YulEvmCompiler.plainOp operation := by
  cases operation <;>
    simp [plainOperation, YulEvmCompiler.plainOp] at valid ⊢

private def wellFormed (fork : Fork) : Instr → Bool
  | .push width value =>
      decide (value.toNat < 256 ^ width.val) &&
        (Operation.Push ⟨width⟩).availableInFork fork
  | .op operation =>
      decide (Decode.opcodeOf (Instr.opByte operation) = some operation) &&
        (plainOperation operation && operation.availableInFork fork)

private theorem wellFormed_valid {fork : Fork} {instruction : Instr}
    (valid : wellFormed fork instruction = true) :
    Stepper.WellFormed fork instruction := by
  cases instruction with
  | push width value =>
      simp only [wellFormed, Bool.and_eq_true] at valid
      exact ⟨of_decide_eq_true valid.1, valid.2⟩
  | op operation =>
      simp only [wellFormed, Bool.and_eq_true] at valid
      exact ⟨of_decide_eq_true valid.1,
        plainOperation_valid operation valid.2.1, valid.2.2⟩

private def allWellFormed (fork : Fork) : List Entry → Bool
  | [] => true
  | row :: rest =>
      wellFormed fork row.instruction && allWellFormed fork rest

private theorem allWellFormed_valid {fork : Fork} {rows : List Entry}
    (valid : allWellFormed fork rows = true) {row : Entry}
    (hmem : row ∈ rows) : Stepper.WellFormed fork row.instruction := by
  induction rows generalizing row with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [allWellFormed, Bool.and_eq_true] at valid
      rcases valid with ⟨hhead, htail⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst row
        exact wellFormed_valid hhead
      · exact ih htail hmem

/-- A table is valid when it assembles to the exact submitted bytes, every
cached offset is exact, and every instruction is available on the selected
fork with a well-formed encoding. -/
def Valid (fork : Fork) (code : ByteArray) (rows : Array Entry) : Prop :=
  assemble (instructions rows) = code ∧
    rows.toList.map (·.pc) = instructionPCs rows ∧
    allWellFormed fork rows.toList = true

instance (fork : Fork) (code : ByteArray) (rows : Array Entry) :
    Decidable (Valid fork code rows) := by
  unfold Valid
  infer_instance

namespace Valid

theorem assembly_eq {fork : Fork} {code : ByteArray} {rows : Array Entry}
    (valid : Valid fork code rows) : assemble (instructions rows) = code :=
  valid.1

theorem pc_eq {fork : Fork} {code : ByteArray} {rows : Array Entry}
    (valid : Valid fork code rows) (index : Fin rows.size) :
    rows[index].pc = instructionPC rows index.val := by
  have h := congrArg (fun pcs : List Nat => pcs[index.val]?) valid.2.1
  have hindex : index.val < rows.toList.length := by
    simp [index.isLt]
  rw [instructionPCs,
    instructionPCsFrom_getElem? 0 rows.toList index.val hindex] at h
  simpa [instructionPC, instructions, index.isLt] using h

theorem wellFormed {fork : Fork} {code : ByteArray} {rows : Array Entry}
    (valid : Valid fork code rows) (index : Fin rows.size) :
    Stepper.WellFormed fork rows[index].instruction := by
  have hi : index.val < rows.toList.length := by
    simp [index.isLt]
  have hmem : rows.toList[index.val] ∈ rows.toList := List.getElem_mem hi
  have hwf := allWellFormed_valid valid.2.2 hmem
  simpa using hwf

end Valid

end Table

end CertifiedArtifact

/-- Exact bytecode together with its certified cached instruction table. -/
structure CertifiedArtifact (fork : Fork) (code : ByteArray) where
  rows : Array CertifiedArtifact.Entry
  valid : CertifiedArtifact.Table.Valid fork code rows

namespace CertifiedArtifact

/-- Package rows after their single whole-table certificate has checked. -/
def certify {fork : Fork} {code : ByteArray} (rows : Array Entry)
    (valid : Table.Valid fork code rows) : CertifiedArtifact fork code :=
  ⟨rows, valid⟩

/-- Compact evidence that a cached entry decodes from stable bytecode and fork
premises.  Its type deliberately contains no artifact row, index, or binding
equality, so downstream soundness proofs cannot unfold a large table. -/
structure DecoderCertificate (fork : Fork) (code : ByteArray)
    (entry : Entry) : Prop where
  decodes : ∀ (state : State),
    state.executionEnv.code = code →
    state.fork = fork →
    state.pc.toNat = entry.pc →
    Stepper.Decodes state entry.instruction

/-- A selected instruction site containing only its cached entry and compact
decoder certificate.  Artifact lookup is discharged before this value enters
a downstream execution proof. -/
structure SelectedEntry (fork : Fork) (code : ByteArray) where
  entry : Entry
  decoder : DecoderCertificate fork code entry

/-- Shared executable semantics for paths whose sites provide cached entries. -/
private def runEntries {Site : Type} (entryOf : Site → Entry) :
    List Site → State → Option (State × Nat)
  | [], state => some (state, 0)
  | site :: rest, state =>
      let entry := entryOf site
      if state.pc.toNat = entry.pc then
        match Stepper.runInstr entry.instruction state with
        | none => none
        | some next =>
            let cost := Stepper.instrCost entry.instruction state
            match rest with
            | [] => some (next, cost)
            | _ :: _ =>
                match next.halt with
                | .Running =>
                    match runEntries entryOf rest next with
                    | none => none
                    | some (finish, restCost) =>
                        some (finish, cost + restCost)
                | _ => none
      else none

/-- Execute a cached path and return the final state with its exact gas cost. -/
def run (artifact : CertifiedArtifact fork code)
    (path : List (Fin artifact.rows.size)) (state : State) :
    Option (State × Nat) :=
  runEntries (fun index => artifact.rows[index]) path state

/-- Execute proof-carrying selected sites without indexing the artifact table.
This is the scalable evaluator for proofs that mention a small path through a
large artifact; `run` remains available as the index-only compatibility API. -/
def runSelected (_artifact : CertifiedArtifact fork code)
    (path : List (SelectedEntry fork code)) (state : State) :
    Option (State × Nat) :=
  runEntries (fun selected => selected.entry) path state

/-- Stable execution premises needed to lift a certified evaluator run into
the relational EVM semantics. -/
structure ExecutionContext (artifact : CertifiedArtifact fork code)
    (start : State) : Prop where
  code_eq : start.executionEnv.code = code
  fork_eq : start.fork = fork
  running : start.halt = .Running
  notPrecompile : Precompile.isPrecompileWithConfig
    start.executionEnv.precompileConfig start.executionEnv.fork
      start.executionEnv.codeAddr = false

private def program (artifact : CertifiedArtifact fork code) : ProgramArtifact where
  code := code
  instructions := instructions artifact.rows
  assembly_eq := artifact.valid.assembly_eq

private theorem row_at_index (artifact : CertifiedArtifact fork code)
    (index : Fin artifact.rows.size) :
    (program artifact).instructions[index.val]? =
      some artifact.rows[index].instruction := by
  simp [program, instructions, index.isLt]

private theorem decodes_at_index (artifact : CertifiedArtifact fork code)
    (index : Fin artifact.rows.size) (state : State)
    (code_eq : state.executionEnv.code = code)
    (fork_eq : state.fork = fork)
    (pc_eq : state.pc.toNat = artifact.rows[index].pc) :
    Stepper.Decodes state artifact.rows[index].instruction := by
  apply Stepper.decodes_of_artifact (program artifact) state index.val
  · simpa [program] using code_eq
  · rw [pc_eq, artifact.valid.pc_eq index]
    rfl
  · exact row_at_index artifact index
  · simpa [fork_eq] using artifact.valid.wellFormed index

/-- Discharge one artifact lookup into a compact decoder certificate.  Give
the resulting proof a name near a large artifact, then build `SelectedEntry`
values from that named certificate so downstream proof terms mention no rows. -/
theorem decoderCertificate (artifact : CertifiedArtifact fork code)
    (index : Fin artifact.rows.size) (entry : Entry)
    (bound : artifact.rows[index] = entry) :
    DecoderCertificate fork code entry := by
  constructor
  intro state code_eq fork_eq pc_eq
  have indexed_pc_eq :
      state.pc.toNat = artifact.rows[index].pc := by
    simpa only [bound] using pc_eq
  have decoded := decodes_at_index artifact index state code_eq fork_eq
    indexed_pc_eq
  simpa only [bound] using decoded

private theorem next_context (artifact : CertifiedArtifact fork code)
    {instruction : Instr} {state next : State}
    (context : ExecutionContext artifact state)
    (result : Stepper.runInstr instruction state = some next)
    (running : next.halt = .Running) :
    ExecutionContext artifact next := by
  have env_eq := Stepper.runInstr_executionEnv result
  refine {
    code_eq := ?_
    fork_eq := ?_
    running := running
    notPrecompile := ?_
  }
  · rw [env_eq]
    exact context.code_eq
  · change next.executionEnv.fork = fork
    rw [env_eq]
    exact context.fork_eq
  · simpa [env_eq] using context.notPrecompile

private def runEntries_sound (artifact : CertifiedArtifact fork code)
    {Site : Type} (entryOf : Site → Entry)
    (decodes : ∀ (site : Site) (state : State),
      ExecutionContext artifact state →
      state.pc.toNat = (entryOf site).pc →
      Stepper.Decodes state (entryOf site).instruction)
    (path : List Site) {start finish : State} {cost : Nat}
    (result : runEntries entryOf path start = some (finish, cost))
    (context : ExecutionContext artifact start) :
    { trace : GasSteps start finish // trace.cost = cost } := by
  induction path generalizing start finish cost with
  | nil =>
      have pair_eq := Option.some.inj result
      have finish_eq := congrArg Prod.fst pair_eq
      have cost_eq := congrArg Prod.snd pair_eq
      simp only at finish_eq cost_eq
      subst finish
      subst cost
      exact ⟨GasSteps.refl start, rfl⟩
  | cons site rest ih =>
      by_cases pc_eq : start.pc.toNat = (entryOf site).pc
      · cases instr_result : Stepper.runInstr (entryOf site).instruction start with
        | none =>
            rw [runEntries, if_pos pc_eq, instr_result] at result
            simp only at result
            cases result
        | some next =>
          cases rest with
          | nil =>
              rw [runEntries, if_pos pc_eq, instr_result] at result
              simp only at result
              have pair_eq := Option.some.inj result
              have finish_eq := congrArg Prod.fst pair_eq
              have cost_eq := congrArg Prod.snd pair_eq
              simp only at finish_eq cost_eq
              subst finish
              subst cost
              let trace := Stepper.runInstr_sound
                (decodes site start context pc_eq)
                instr_result context.running context.notPrecompile
              exact ⟨trace, rfl⟩
          | cons nextSite tail =>
            rw [runEntries, if_pos pc_eq, instr_result] at result
            simp only at result
            cases next_running : next.halt with
            | Running =>
              cases rest_result :
                  runEntries entryOf (nextSite :: tail) next with
              | none =>
                  rw [next_running, rest_result] at result
                  simp only at result
                  cases result
              | some rest_pair =>
                rcases rest_pair with ⟨rest_finish, rest_cost⟩
                rw [next_running, rest_result] at result
                simp only at result
                have pair_eq := Option.some.inj result
                have finish_eq := congrArg Prod.fst pair_eq
                have cost_eq := congrArg Prod.snd pair_eq
                simp only at finish_eq cost_eq
                subst finish
                subst cost
                let head := Stepper.runInstr_sound
                  (decodes site start context pc_eq)
                  instr_result context.running context.notPrecompile
                obtain ⟨rest_trace, rest_cost_eq⟩ := ih rest_result
                  (next_context artifact context instr_result next_running)
                exact ⟨head.trans rest_trace, by simp [head, rest_cost_eq]⟩
            | Success =>
                rw [next_running] at result
                simp only at result
                cases result
            | Returned =>
                rw [next_running] at result
                simp only at result
                cases result
            | Reverted =>
                rw [next_running] at result
                simp only at result
                cases result
            | Exception error =>
                rw [next_running] at result
                simp only at result
                cases result
      · rw [runEntries, if_neg pc_eq] at result
        cases result

/-- A successful cached execution path denotes a relational trace with exactly
the cost computed by `run`. -/
def run_sound (artifact : CertifiedArtifact fork code)
    (path : List (Fin artifact.rows.size)) {start finish : State} {cost : Nat}
    (result : artifact.run path start = some (finish, cost))
    (context : ExecutionContext artifact start) :
    { trace : GasSteps start finish // trace.cost = cost } :=
  runEntries_sound artifact (fun index => artifact.rows[index])
    (fun index state executionContext pc_eq =>
      decodes_at_index artifact index state executionContext.code_eq
        executionContext.fork_eq pc_eq)
    path result context

/-- A successful selected-site execution denotes a relational trace with the
exact cost computed by `runSelected`.  Artifact indices and binding equalities
have already been discharged into compact certificates; this theorem consumes
only each carried entry and its decoder. -/
def runSelected_sound (artifact : CertifiedArtifact fork code)
    (path : List (SelectedEntry fork code)) {start finish : State} {cost : Nat}
    (result : artifact.runSelected path start = some (finish, cost))
    (context : ExecutionContext artifact start) :
    { trace : GasSteps start finish // trace.cost = cost } :=
  runEntries_sound artifact
    (fun selected : SelectedEntry fork code => selected.entry)
    (fun selected state executionContext pc_eq =>
      selected.decoder.decodes state executionContext.code_eq
        executionContext.fork_eq pc_eq)
    path result context

/-- Proposition-valued sealing boundary for selected-site soundness.  Apply
this theorem directly when only existence of an exact-cost trace is needed:
because theorem bodies are opaque downstream, a concrete path does not force
normalization of the Type-valued trace produced by `runSelected_sound`. -/
theorem runSelected_sound_exists (artifact : CertifiedArtifact fork code)
    (path : List (SelectedEntry fork code)) {start finish : State} {cost : Nat}
    (result : artifact.runSelected path start = some (finish, cost))
    (context : ExecutionContext artifact start) :
    ∃ trace : GasSteps start finish, trace.cost = cost := by
  obtain ⟨trace, hcost⟩ := artifact.runSelected_sound path result context
  exact ⟨trace, hcost⟩

end CertifiedArtifact

end Challenge.EvmProof
