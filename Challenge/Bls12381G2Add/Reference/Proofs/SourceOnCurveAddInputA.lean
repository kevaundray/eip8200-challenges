import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveConstantMemory

set_option warningAsError true

/-! # Left scheduled input for frozen G2ADD `onCurve` addition -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem onCurveAdd_scheduledA_c1 (yst : EvmState) (x y : U256) :
    (fp2AddScheduledA (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2432)).c1 =
    (fp2At (onCurveStateAfterX3 yst x y)
      (BitVec.ofNat 256 2304)).c1 := by
  unfold fp2AddScheduledA fp2AddAfterC0Stores fp2AddAfterC0High fp2At
  change ({
    hi := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (onCurveStateAfterConstant yst x y).memory
        2304 _) 2336 _) 2368)
    lo := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (onCurveStateAfterConstant yst x y).memory
        2304 _) 2336 _) 2400) } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) = _
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by norm_num)]
  exact congrArg Challenge.Bls12381.ProofSupport.Fp2.Repr.c1
    (onCurveConstant_x3 yst x y)

theorem onCurveAdd_scheduledA (yst : EvmState) (x y : U256) :
    fp2AddScheduledA (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432) =
      fp2At (onCurveStateAfterX3 yst x y) (BitVec.ofNat 256 2304) := by
  have h0 :
      (fp2AddScheduledA (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432)).c0 =
      (fp2At (onCurveStateAfterX3 yst x y)
        (BitVec.ofNat 256 2304)).c0 := by
    simpa only [fp2AddScheduledA] using
      congrArg Challenge.Bls12381.ProofSupport.Fp2.Repr.c0
        (onCurveConstant_x3 yst x y)
  have h1 := onCurveAdd_scheduledA_c1 yst x y
  generalize hleft : fp2AddScheduledA (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2432) = left at h0 h1 ⊢
  generalize hright : fp2At (onCurveStateAfterX3 yst x y)
      (BitVec.ofNat 256 2304) = right at h0 h1 ⊢
  cases left
  cases right
  simp only [Challenge.Bls12381.ProofSupport.Fp2.Repr.mk.injEq] at ⊢ h0 h1
  exact ⟨h0, h1⟩

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
