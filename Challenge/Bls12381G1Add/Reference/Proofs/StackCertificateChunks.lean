import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk0
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk1
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk2
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk3
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk4
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk5
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk6
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk7
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk8
import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk9

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

set_option maxRecDepth 10000 in
theorem referenceStackLengthEntryChecks :
    stackLengthEntryChecks referenceStackCertificate.entries = true := by
  have h10 : stackLengthEntryChecks
      (referenceStackCertificate.entries.drop 1000) = true := by
    rfl
  have h9 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 900) 100
    stackLengthEntryChecks_chunk9 h10
  have h8 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 800) 100
    stackLengthEntryChecks_chunk8 (by simpa [List.drop_drop] using h9)
  have h7 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 700) 100
    stackLengthEntryChecks_chunk7 (by simpa [List.drop_drop] using h8)
  have h6 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 600) 100
    stackLengthEntryChecks_chunk6 (by simpa [List.drop_drop] using h7)
  have h5 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 500) 100
    stackLengthEntryChecks_chunk5 (by simpa [List.drop_drop] using h6)
  have h4 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 400) 100
    stackLengthEntryChecks_chunk4 (by simpa [List.drop_drop] using h5)
  have h3 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 300) 100
    stackLengthEntryChecks_chunk3 (by simpa [List.drop_drop] using h4)
  have h2 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 200) 100
    stackLengthEntryChecks_chunk2 (by simpa [List.drop_drop] using h3)
  have h1 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 100) 100
    stackLengthEntryChecks_chunk1 (by simpa [List.drop_drop] using h2)
  exact stackLengthEntryChecks_take_drop
    referenceStackCertificate.entries 100
    stackLengthEntryChecks_chunk0 (by simpa [List.drop_drop] using h1)

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
