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

/-- Execute a cached path and return the final state with its exact gas cost. -/
def run (artifact : CertifiedArtifact fork code) :
    List (Fin artifact.rows.size) → State → Option (State × Nat)
  | [], state => some (state, 0)
  | index :: rest, state =>
      let entry := artifact.rows[index]
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
                    match run artifact rest next with
                    | none => none
                    | some (finish, restCost) =>
                        some (finish, cost + restCost)
                | _ => none
      else none

end CertifiedArtifact

end Challenge.EvmProof
