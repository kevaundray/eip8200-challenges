import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveAddInputB

set_option warningAsError true

/-! # Lawful right-hand side of frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem onCurveRhs_canonical (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.Canonical (fp2At (onCurveStateAfterAdd yst x y)
      (BitVec.ofNat 256 2304)) := by
  rw [onCurveStateAfterAdd, fp2AddFinalState_output _ _ _ _ (by norm_num)]
  apply fp2AddResult_canonical
  · rw [onCurveAdd_scheduledA]
    exact onCurveX3_canonical yst x y hx hxEnd hxLow
  · rw [onCurveAdd_scheduledB]
    exact onCurveTwistB_canonical

theorem onCurveRhs_toLawful (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.toLawful (fp2At (onCurveStateAfterAdd yst x y)
        (BitVec.ofNat 256 2304)) =
      Fp2.toLawful (fp2At yst x) ^ 3 + G2Affine.curve.b := by
  have ha : Fp2.Canonical
      (fp2AddScheduledA (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432)) := by
    rw [onCurveAdd_scheduledA]
    exact onCurveX3_canonical yst x y hx hxEnd hxLow
  have hb : Fp2.Canonical
      (fp2AddScheduledB (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432)) := by
    rw [onCurveAdd_scheduledB]
    exact onCurveTwistB_canonical
  rw [onCurveStateAfterAdd, fp2AddFinalState_output _ _ _ _ (by norm_num),
    fp2AddResult_eq_addSource, Fp2.toLawful_addSource ha hb]
  rw [onCurveAdd_scheduledA, onCurveAdd_scheduledB,
    onCurveX3_toLawful yst x y hx hxEnd hxLow, onCurveTwistB_toLawful]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
