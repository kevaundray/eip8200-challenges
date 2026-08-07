import Challenge.EvmProof.CertifiedArtifact

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
