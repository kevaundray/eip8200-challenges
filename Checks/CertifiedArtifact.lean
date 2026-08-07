import Challenge.EvmProof.CertifiedArtifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Spec

namespace Checks.CertifiedArtifact

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof

def rows : Array CertifiedArtifact.Entry := #[
  ⟨0, .push 2 258⟩,
  ⟨3, .push 0 0⟩,
  ⟨4, .op .ADD⟩
]

def code : ByteArray := assemble (rows.toList.map (·.instruction))

theorem rows_valid : CertifiedArtifact.Table.Valid .Osaka code rows := by
  decide

def artifact : CertifiedArtifact .Osaka code :=
  CertifiedArtifact.certify rows rows_valid

def path : List (Fin artifact.rows.size) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

def start : EVM.State :=
  Challenge.Ripemd160.initialState code ByteArray.empty 0

def finish : EVM.State :=
  { start with pc := 5, stack := [258] }

theorem run_tiny : artifact.run path start = some (finish, 8) := by
  rfl

def context : CertifiedArtifact.ExecutionContext artifact start where
  code_eq := rfl
  fork_eq := rfl
  running := rfl
  notPrecompile := Challenge.Ripemd160.deployAddress_not_precompile

theorem tiny_sound : ∃ trace : GasSteps start finish, trace.cost = 8 := by
  obtain ⟨trace, hcost⟩ := artifact.run_sound path run_tiny context
  exact ⟨trace, hcost⟩

example : artifact.run [] start = some (start, 0) := by
  rfl

def firstPath : List (Fin artifact.rows.size) := [⟨0, by decide⟩]

def afterFirst : EVM.State :=
  { start with pc := 3, stack := [258] }

example : artifact.run firstPath start = some (afterFirst, 3) := by
  rfl

def wrongPC : EVM.State :=
  { start with pc := 1 }

example : artifact.run firstPath wrongPC = none := by
  rfl

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
  Challenge.Ripemd160.initialState haltingCode ByteArray.empty 0

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
