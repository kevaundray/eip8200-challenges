import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveAddInputA

set_option warningAsError true

/-! # Right scheduled input for frozen G2ADD `onCurve` addition -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem onCurveAdd_scheduledB_c1 (yst : EvmState) (x y : U256) :
    (fp2AddScheduledB (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2432)).c1 = onCurveTwistB.c1 := by
  unfold fp2AddScheduledB fp2AddAfterC0Stores fp2AddAfterC0High fp2At
  change ({
    hi := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (onCurveStateAfterConstant yst x y).memory
        2304 _) 2336 _) 2496)
    lo := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (onCurveStateAfterConstant yst x y).memory
        2304 _) 2336 _) 2528) } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) = _
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by norm_num)]
  exact congrArg Challenge.Bls12381.ProofSupport.Fp2.Repr.c1
    (onCurveConstant_value yst x y)

theorem onCurveAdd_scheduledB (yst : EvmState) (x y : U256) :
    fp2AddScheduledB (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432) = onCurveTwistB := by
  have h0 :
      (fp2AddScheduledB (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432)).c0 = onCurveTwistB.c0 := by
    simpa only [fp2AddScheduledB] using
      congrArg Challenge.Bls12381.ProofSupport.Fp2.Repr.c0
        (onCurveConstant_value yst x y)
  have h1 := onCurveAdd_scheduledB_c1 yst x y
  generalize hleft : fp2AddScheduledB (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2432) = left at h0 h1 ⊢
  generalize hright : onCurveTwistB = right at h0 h1 ⊢
  cases left
  cases right
  simp only [Challenge.Bls12381.ProofSupport.Fp2.Repr.mk.injEq] at ⊢ h0 h1
  exact ⟨h0, h1⟩

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
