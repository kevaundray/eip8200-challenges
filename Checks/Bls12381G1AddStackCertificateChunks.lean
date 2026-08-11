import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunks

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

example : stackLengthEntryChecks referenceStackCertificate.entries = true :=
  referenceStackLengthEntryChecks

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceStackLengthEntryChecks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms referenceStackLengthEntryChecks
