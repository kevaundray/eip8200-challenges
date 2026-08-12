import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateCore

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

private def entries := frozenStackEntries
private def chunkEntries := (entries.drop 200).take 100

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk2 :
    stackFrozenEntryChecks ((entries.drop 200).take 100) = true
  using chunkEntries with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
