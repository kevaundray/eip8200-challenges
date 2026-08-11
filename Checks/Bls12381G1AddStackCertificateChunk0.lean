import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk0

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

example : stackLengthEntryChecks
    (referenceStackCertificate.entries.take 100) = true :=
  stackLengthEntryChecks_chunk0
