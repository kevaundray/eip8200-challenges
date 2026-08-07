import Challenge.EvmProof

namespace Checks.CertifiedArtifact

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof

/-! Typed disassembly constructs certified rows directly from submitted bytes. -/

def disassembledCode : ByteArray := ByteArray.mk #[0x61, 0x01, 0x02, 0x01]

def disassembledRows : Array CertifiedArtifact.Entry :=
  CertifiedArtifact.rowsOfBytecode disassembledCode

example : disassembledRows = #[
    ⟨0, .push 2 258⟩,
    ⟨3, .op .ADD⟩
  ] := by
  rfl

example :
    (Challenge.EvmProof.Bytecode.disassemble disassembledCode).map
      RawInstr.toCandidate = [.push 2 258, .op .ADD] := by
  rfl

example : RawInstr.accepted .Osaka
    { opcode := 0x61, immediate := [0x01, 0x02] } = true := by
  decide

example : RawInstr.accepted .Osaka
    { opcode := 0x61, immediate := [0xaa] } = false := by
  decide

example : RawInstr.accepted .Osaka
    { opcode := 0xe6, immediate := [0x01] } = false := by
  decide

example : RawInstr.accepted .Osaka
    { opcode := 0x0c, immediate := [] } = false := by
  decide

theorem disassembledCertificate :
    CertifiedArtifact.BytecodeCertificate .Osaka disassembledCode := by
  decide

def disassembledArtifact : CertifiedArtifact .Osaka disassembledCode :=
  CertifiedArtifact.fromBytecode disassembledCertificate

example : disassembledArtifact.rows = disassembledRows := rfl

example : assemble (CertifiedArtifact.instructions disassembledArtifact.rows) =
    disassembledCode :=
  disassembledArtifact.valid.assembly_eq

def rows : Array CertifiedArtifact.Entry := #[
  ⟨0, .push 2 258⟩,
  ⟨3, .push 0 0⟩,
  ⟨4, .op .ADD⟩
]

def code : ByteArray := assemble (rows.toList.map (·.instruction))

def testAddress : AccountAddress := AccountAddress.ofNat 0x8200
def testPrecompileConfig : PrecompileConfig := { disabled := [] }

/-- Minimal challenge-independent execution frame for stepper checks. -/
def testState (program : ByteArray) : EVM.State :=
  { (default : EVM.State) with
    pc := 0
    stack := []
    halt := .Running
    executionEnv := {
      (default : ExecutionEnv) with
      code := program
      codeAddr := testAddress
      fork := .Osaka
      precompileConfig := testPrecompileConfig
    }
  }

theorem testAddress_not_precompile :
    Precompile.isPrecompileWithConfig testPrecompileConfig
      .Osaka testAddress = false := by
  decide

theorem rows_valid : CertifiedArtifact.Table.Valid .Osaka code rows := by
  decide

def artifact : CertifiedArtifact .Osaka code :=
  CertifiedArtifact.certify rows rows_valid

def path : List (Fin artifact.rows.size) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

def start : EVM.State :=
  testState code

def finish : EVM.State :=
  { start with pc := 5, stack := [258] }

theorem run_tiny : artifact.run path start = some (finish, 8) := by
  rfl

def context : CertifiedArtifact.ExecutionContext artifact start where
  code_eq := rfl
  fork_eq := rfl
  running := rfl
  notPrecompile := testAddress_not_precompile

theorem tiny_sound : ∃ trace : GasSteps start finish, trace.cost = 8 := by
  obtain ⟨trace, hcost⟩ := artifact.run_sound path run_tiny context
  exact ⟨trace, hcost⟩

theorem row0_decoder : CertifiedArtifact.DecoderCertificate
    .Osaka code ⟨0, .push 2 258⟩ :=
  artifact.decoderCertificate ⟨0, by decide⟩ ⟨0, .push 2 258⟩ rfl

theorem row1_decoder : CertifiedArtifact.DecoderCertificate
    .Osaka code ⟨3, .push 0 0⟩ :=
  artifact.decoderCertificate ⟨1, by decide⟩ ⟨3, .push 0 0⟩ rfl

theorem row2_decoder : CertifiedArtifact.DecoderCertificate
    .Osaka code ⟨4, .op .ADD⟩ :=
  artifact.decoderCertificate ⟨2, by decide⟩ ⟨4, .op .ADD⟩ rfl

def selectedPath : List (CertifiedArtifact.SelectedEntry .Osaka code) :=
  [⟨⟨0, .push 2 258⟩, row0_decoder⟩,
   ⟨⟨3, .push 0 0⟩, row1_decoder⟩,
   ⟨⟨4, .op .ADD⟩, row2_decoder⟩]

theorem run_selected_tiny :
    artifact.runSelected selectedPath start = some (finish, 8) := by
  rfl

/-- Client-style reduction uses only public selected-path equations, never the
private shared evaluator. -/
theorem run_selected_tiny_by_equations :
    artifact.runSelected selectedPath start = some (finish, 8) := by
  simp only [selectedPath, CertifiedArtifact.runSelected_cons]
  rfl

def afterFirst : EVM.State :=
  { start with pc := 3, stack := [258] }

theorem run_selected_first :
    artifact.runSelected [selectedPath[0]] start = some (afterFirst, 3) := by
  rfl

def selectedRestPath : List (CertifiedArtifact.SelectedEntry .Osaka code) :=
  [selectedPath[1], selectedPath[2]]

theorem run_selected_rest :
    artifact.runSelected selectedRestPath afterFirst = some (finish, 5) := by
  rfl

/-- A longer result composes opaque segment facts rather than reducing the
whole selected evaluator at once. -/
theorem run_selected_composed :
    artifact.runSelected ([selectedPath[0]] ++ selectedRestPath) start =
      some (finish, 3 + 5) :=
  artifact.runSelected_append [selectedPath[0]] selectedRestPath
    run_selected_first rfl run_selected_rest

example : artifact.runSelected ([] ++ selectedPath) start =
    some (finish, 0 + 8) :=
  artifact.runSelected_append [] selectedPath rfl rfl run_selected_tiny

example : artifact.runSelected ([selectedPath[0]] ++ []) start =
    some (afterFirst, 3 + 0) :=
  artifact.runSelected_append [selectedPath[0]] [] run_selected_first rfl rfl

theorem selected_tiny_sound : ∃ trace : GasSteps start finish, trace.cost = 8 := by
  obtain ⟨trace, hcost⟩ :=
    artifact.runSelected_sound selectedPath run_selected_tiny context
  exact ⟨trace, hcost⟩

theorem selected_tiny_sound_exists :
    ∃ trace : GasSteps start finish, trace.cost = 8 :=
  artifact.runSelected_sound_exists selectedPath run_selected_tiny context

example : artifact.run [] start = some (start, 0) := by
  rfl

example : artifact.runSelected [] start = some (start, 0) := by
  rfl

def firstPath : List (Fin artifact.rows.size) := [⟨0, by decide⟩]

example : artifact.run firstPath start = some (afterFirst, 3) := by
  rfl

def wrongPC : EVM.State :=
  { start with pc := 1 }

example : artifact.run firstPath wrongPC = none := by
  rfl

def selectedFirst : CertifiedArtifact.SelectedEntry .Osaka code :=
  ⟨⟨0, .push 2 258⟩, row0_decoder⟩

def selectedFirstPath : List (CertifiedArtifact.SelectedEntry .Osaka code) :=
  [selectedFirst]

example : artifact.runSelected selectedFirstPath start = some (afterFirst, 3) := by
  rfl

example : artifact.runSelected selectedFirstPath wrongPC = none := by
  rfl

def addUnderflow : EVM.State :=
  { start with pc := 4 }

def selectedAdd : CertifiedArtifact.SelectedEntry .Osaka code :=
  ⟨⟨4, .op .ADD⟩, row2_decoder⟩

example : artifact.runSelected [selectedAdd] addUnderflow = none := by
  rfl

/-- Reduction guard: even when the certified artifact is abstract, selected
execution computes from the carried snapshot rather than indexing its table. -/
example (abstractArtifact : CertifiedArtifact .Osaka code)
    (decoder : CertifiedArtifact.DecoderCertificate
      .Osaka code ⟨0, .push 2 258⟩) :
    abstractArtifact.runSelected
      [⟨⟨0, .push 2 258⟩, decoder⟩] start =
        some (afterFirst, 3) := by
  rfl

/-- Soundness guard: the selected path and its decoder are compact, so an
abstract artifact supplies only the stable execution context, never a row. -/
theorem abstract_selected_sound
    (abstractArtifact : CertifiedArtifact .Osaka code)
    (decoder : CertifiedArtifact.DecoderCertificate
      .Osaka code ⟨0, .push 2 258⟩) :
    ∃ trace : GasSteps start afterFirst, trace.cost = 3 := by
  let selected : CertifiedArtifact.SelectedEntry .Osaka code :=
    ⟨⟨0, .push 2 258⟩, decoder⟩
  have result : abstractArtifact.runSelected [selected] start =
      some (afterFirst, 3) := by
    rfl
  let abstractContext :
      CertifiedArtifact.ExecutionContext abstractArtifact start := {
    code_eq := rfl
    fork_eq := rfl
    running := rfl
    notPrecompile := testAddress_not_precompile
  }
  exact abstractArtifact.runSelected_sound_exists [selected] result
    abstractContext

def haltingRows : Array CertifiedArtifact.Entry := #[
  ⟨0, .op .INVALID⟩,
  ⟨1, .push 0 0⟩
]

def haltingCode : ByteArray :=
  assemble (haltingRows.toList.map (·.instruction))

theorem haltingRows_valid :
    CertifiedArtifact.Table.Valid .Osaka haltingCode haltingRows := by
  decide

def haltingArtifact : CertifiedArtifact .Osaka haltingCode :=
  CertifiedArtifact.certify haltingRows haltingRows_valid

def haltingStart : EVM.State :=
  testState haltingCode

def halted : EVM.State :=
  { haltingStart with halt := .Exception .InvalidInstruction }

def haltingPath : List (Fin haltingArtifact.rows.size) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩]

example : haltingArtifact.run haltingPath haltingStart = none := by
  rfl

def haltOnlyPath : List (Fin haltingArtifact.rows.size) :=
  [⟨0, by decide⟩]

example : haltingArtifact.run haltOnlyPath haltingStart = some (halted, 0) := by
  rfl

theorem halting0_decoder : CertifiedArtifact.DecoderCertificate
    .Osaka haltingCode ⟨0, .op .INVALID⟩ :=
  haltingArtifact.decoderCertificate ⟨0, by decide⟩
    ⟨0, .op .INVALID⟩ rfl

theorem halting1_decoder : CertifiedArtifact.DecoderCertificate
    .Osaka haltingCode ⟨1, .push 0 0⟩ :=
  haltingArtifact.decoderCertificate ⟨1, by decide⟩
    ⟨1, .push 0 0⟩ rfl

def selectedHaltingPath :
    List (CertifiedArtifact.SelectedEntry .Osaka haltingCode) :=
  [⟨⟨0, .op .INVALID⟩, halting0_decoder⟩,
   ⟨⟨1, .push 0 0⟩, halting1_decoder⟩]

example : haltingArtifact.runSelected selectedHaltingPath haltingStart = none := by
  rfl

example : halted.halt ≠ .Running := by
  simp [halted]

def selectedHaltOnlyPath :
    List (CertifiedArtifact.SelectedEntry .Osaka haltingCode) :=
  [⟨⟨0, .op .INVALID⟩, halting0_decoder⟩]

example :
    haltingArtifact.runSelected selectedHaltOnlyPath haltingStart =
      some (halted, 0) := by
  rfl

example : ¬ CertifiedArtifact.Table.Valid .Osaka ByteArray.empty rows := by
  decide

def staleRows : Array CertifiedArtifact.Entry := rows.set! 1 ⟨7, .push 0 0⟩

example : ¬ CertifiedArtifact.Table.Valid .Osaka code staleRows := by
  decide

def malformedRows : Array CertifiedArtifact.Entry := #[
  ⟨0, .push 0 1⟩
]

def malformedCode : ByteArray :=
  assemble (malformedRows.toList.map (·.instruction))

example : ¬ CertifiedArtifact.Table.Valid .Osaka malformedCode malformedRows := by
  decide

end Checks.CertifiedArtifact
