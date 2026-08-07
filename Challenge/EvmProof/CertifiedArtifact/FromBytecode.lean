import Challenge.EvmProof.Bytecode
import Challenge.EvmProof.CertifiedArtifact

set_option warningAsError true

/-!
# Certified artifacts derived from submitted bytecode

This module turns the byte-preserving raw disassembly into the compiler's
typed instruction view.  A single linear Boolean certificate rejects chunks
that cannot be represented exactly by that view, including truncated PUSHes,
unknown opcodes, and EIP-8024 instructions with extended immediates.
-/

namespace Challenge.EvmProof

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

namespace RawInstr

private def immediateValue (raw : RawInstr) : UInt256 :=
  UInt256.ofNat
    (raw.immediate.foldl (fun value byte => value * 256 + byte.toNat) 0)

/-- Best typed instruction represented by a raw chunk.  Acceptance separately
checks that this candidate reassembles to the exact original chunk. -/
def toCandidate (raw : RawInstr) : Instr :=
  match raw.opcodeOperation? with
  | some (.Push width) => .push width.width raw.immediateValue
  | some operation => .op operation
  | none => .op .INVALID

/-- The candidate must preserve every byte and satisfy the selected fork's
typed encoding rules. -/
def accepted (fork : Fork) (raw : RawInstr) : Bool :=
  decide (raw.toCandidate.bytes = raw.bytes) &&
    CertifiedArtifact.Table.wellFormedBool fork raw.toCandidate

theorem bytes_eq_of_accepted {fork : Fork} {raw : RawInstr}
    (valid : raw.accepted fork = true) :
    raw.toCandidate.bytes = raw.bytes := by
  simp only [accepted, Bool.and_eq_true] at valid
  exact of_decide_eq_true valid.1

theorem wellFormed_of_accepted {fork : Fork} {raw : RawInstr}
    (valid : raw.accepted fork = true) :
    Stepper.WellFormed fork raw.toCandidate := by
  simp only [accepted, Bool.and_eq_true] at valid
  exact CertifiedArtifact.Table.wellFormedBool_valid valid.2

end RawInstr

namespace CertifiedArtifact

/-- Cache typed instructions and their byte offsets in one structural pass. -/
def rowsFrom : Nat → List RawInstr → List Entry
  | _, [] => []
  | pc, raw :: rest =>
      { pc, instruction := raw.toCandidate } ::
        rowsFrom (pc + raw.toCandidate.bytes.length) rest

/-- Typed cached rows derived directly from a submitted byte array. -/
def rowsOfBytecode (code : ByteArray) : Array Entry :=
  (rowsFrom 0 (Bytecode.disassemble code)).toArray

/-- One executable certificate validates every raw chunk before it is admitted
to the typed instruction view. -/
def BytecodeCertificate (fork : Fork) (code : ByteArray) : Prop :=
  (Bytecode.disassemble code).all (RawInstr.accepted fork) = true

instance (fork : Fork) (code : ByteArray) :
    Decidable (BytecodeCertificate fork code) := by
  unfold BytecodeCertificate
  infer_instance

private theorem rowsFrom_instructions (pc : Nat) (raws : List RawInstr) :
    (rowsFrom pc raws).map (·.instruction) = raws.map RawInstr.toCandidate := by
  induction raws generalizing pc with
  | nil => rfl
  | cons raw rest ih =>
      simp [rowsFrom, ih]

private theorem rowsFrom_sequential (pc : Nat) (raws : List RawInstr) :
    Table.SequentialFrom pc (rowsFrom pc raws) := by
  induction raws generalizing pc with
  | nil => simp [rowsFrom, Table.SequentialFrom]
  | cons raw rest ih =>
      exact ⟨rfl, ih _⟩

private theorem assembleBytes_candidates {fork : Fork}
    {raws : List RawInstr}
    (valid : raws.all (RawInstr.accepted fork) = true) :
    assembleBytes (raws.map RawInstr.toCandidate) =
      Bytecode.assembleList raws := by
  induction raws with
  | nil => rfl
  | cons raw rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at valid
      rw [List.map_cons, assembleBytes_cons,
        RawInstr.bytes_eq_of_accepted valid.1, ih valid.2]
      rfl

private theorem rowsFrom_wellFormed {fork : Fork} {pc : Nat}
    {raws : List RawInstr}
    (valid : raws.all (RawInstr.accepted fork) = true) :
    ∀ row ∈ rowsFrom pc raws,
      Stepper.WellFormed fork row.instruction := by
  induction raws generalizing pc with
  | nil => simp [rowsFrom]
  | cons raw rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at valid
      intro row hmem
      simp only [rowsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact RawInstr.wellFormed_of_accepted valid.1
      · exact ih valid.2 row hmem

/-- The derived rows satisfy exact assembly, exact cached PCs, and fork
well-formedness.  Only the linear chunk certificate is reduced concretely. -/
theorem rowsOfBytecode_valid {fork : Fork} {code : ByteArray}
    (certificate : BytecodeCertificate fork code) :
    Table.Valid fork code (rowsOfBytecode code) := by
  apply Table.Valid.ofComponents
  · apply ByteArray.ext
    change (assembleBytes
      ((rowsFrom 0 (Bytecode.disassemble code)).toArray.toList.map
        (·.instruction))).toArray = code.data
    rw [List.toList_toArray, rowsFrom_instructions,
      assembleBytes_candidates certificate]
    exact congrArg ByteArray.data (Bytecode.assemble_disassemble code)
  · simpa [rowsOfBytecode] using
      rowsFrom_sequential 0 (Bytecode.disassemble code)
  · intro row hmem
    apply rowsFrom_wellFormed certificate row
    simpa [rowsOfBytecode] using hmem

/-- Package a submitted byte array after its one linear certificate. -/
def fromBytecode {fork : Fork} {code : ByteArray}
    (certificate : BytecodeCertificate fork code) :
    CertifiedArtifact fork code :=
  certify (rowsOfBytecode code) (rowsOfBytecode_valid certificate)

end CertifiedArtifact
end Challenge.EvmProof
