import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk0
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk1
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk2
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk3
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk4
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk5
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk6
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk7
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk8
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk9
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk10
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk11
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk12
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk13
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk14

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

set_option maxRecDepth 10000 in
theorem referenceStackLengthEntryChecks :
    stackLengthEntryChecks referenceStackCertificate.entries = true := by
  have h15 : stackLengthEntryChecks
      (referenceStackCertificate.entries.drop 1500) = true := by
    rfl
  have h14 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1400) 100
    stackLengthEntryChecks_chunk14 (by simpa [List.drop_drop] using h15)
  have h13 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1300) 100
    stackLengthEntryChecks_chunk13 (by simpa [List.drop_drop] using h14)
  have h12 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1200) 100
    stackLengthEntryChecks_chunk12 (by simpa [List.drop_drop] using h13)
  have h11 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1100) 100
    stackLengthEntryChecks_chunk11 (by simpa [List.drop_drop] using h12)
  have h10 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1000) 100
    stackLengthEntryChecks_chunk10 (by simpa [List.drop_drop] using h11)
  have h9 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 900) 100
    stackLengthEntryChecks_chunk9 (by simpa [List.drop_drop] using h10)
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

/-! The public soundness bridge belongs at the aggregate certificate boundary:
the individual chunk modules remain data/decision memory firebreaks. -/

open YulEvmCompiler

abbrev referenceSuffixLookup : CertLookup :=
  Challenge.EvmProof.StackCertificate.suffixLookup
    referenceOptimizedAssembly frozenStackEntries

abbrev referenceCheckedCert : Cert :=
  Challenge.EvmProof.StackCertificate.checkedCert
    referenceOptimizedAssembly frozenStackEntries

theorem referenceSuffixLookup_eq {suffix : List Asm}
    (h : suffix <:+ referenceOptimizedAssembly) :
    referenceSuffixLookup suffix = referenceLengthLookup suffix :=
  Challenge.EvmProof.StackCertificate.suffixLookup_eq h

theorem frameStep_checked_iff_length {instruction : Asm}
    {suffix : List Asm} {stack : FLayout} {frameBase : Nat}
    {returns : FLayout}
    (hpos : instruction :: suffix <:+ referenceOptimizedAssembly) :
    frameStep referenceOptimizedAssembly referenceCheckedCert instruction
        suffix stack frameBase returns ↔
      frameStep referenceOptimizedAssembly referenceLengthLookup.toCert
        instruction suffix stack frameBase returns :=
  Challenge.EvmProof.StackCertificate.frameStep_checked_iff_length hpos

private theorem sharedChecks :
    Challenge.EvmProof.StackCertificate.lengthEntryChecks
      referenceOptimizedAssembly
      (Challenge.EvmProof.StackCertificate.lengthLookup frozenStackEntries)
      (Challenge.EvmProof.StackCertificate.certificateData
        referenceOptimizedAssembly frozenStackEntries).entries = true := by
  exact referenceStackLengthEntryChecks

theorem referenceCheckedCert_valid :
    referenceCheckedCert.Valid referenceOptimizedAssembly :=
  Challenge.EvmProof.StackCertificate.checkedCert_valid
    referenceOptimizedAssembly frozenStackEntries sharedChecks

theorem referenceCheckedCert_bounded : referenceCheckedCert.Bounded :=
  Challenge.EvmProof.StackCertificate.checkedCert_bounded
    referenceOptimizedAssembly frozenStackEntries sharedChecks

set_option maxRecDepth 10000 in
theorem referenceLengthLookup_entry :
    referenceLengthLookup referenceOptimizedAssembly = some ([], 0, []) := by
  with_unfolding_all decide

theorem referenceCheckedCert_entry :
    referenceCheckedCert.fl referenceOptimizedAssembly = some [] ∧
      referenceCheckedCert.fbMax referenceOptimizedAssembly = some 0 ∧
      referenceCheckedCert.rl referenceOptimizedAssembly = some [] :=
  Challenge.EvmProof.StackCertificate.checkedCert_entry
    referenceLengthLookup_entry

variable [model : ExternalModel]

theorem referenceAssembly_stack_bound (state : YulSemantics.EVM.EvmState) :
    ∀ mid, ASteps (model := model) referenceOptimizedAssembly
      ⟨referenceOptimizedAssembly, [], state⟩ mid → mid.stk.length ≤ 1023 :=
  Challenge.EvmProof.StackCertificate.assembly_stack_bound
    referenceOptimizedAssembly frozenStackEntries sharedChecks
      referenceLengthLookup_entry state

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
