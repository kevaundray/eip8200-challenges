import Challenge.EvmProof.CertifiedArtifact
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

example : artifact.run path start = some (finish, 8) := by
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
