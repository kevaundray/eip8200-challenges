import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunks

set_option warningAsError true

/-! # Soundness bridge for the compact G2ADD stack certificate -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

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
