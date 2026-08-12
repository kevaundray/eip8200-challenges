import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainDoubleNumerator
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation

set_option warningAsError true

/-! # Lawful denominator phase of frozen G2ADD doubling -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem mainDoubleState0_y (yst : EvmState) :
    fp2At (mainDoubleState0 yst) 128 = fp2At (mainValidatedState yst) 128 := by
  unfold mainDoubleState0
  exact (fp2MulFinalState_fp2At_before_scratch _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)).trans
      (mainAfterDoubleYZero_fp2At yst 128)

private theorem mainDoubleState1_y (yst : EvmState) :
    fp2At (mainDoubleState1 yst) 128 = fp2At (mainValidatedState yst) 128 := by
  unfold mainDoubleState1
  exact (fp2AddFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainDoubleState0_y yst)

theorem mainDoubleState2_y (yst : EvmState) :
    fp2At (mainDoubleState2 yst) 128 = fp2At (mainValidatedState yst) 128 := by
  unfold mainDoubleState2
  exact (fp2AddFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainDoubleState1_y yst)

theorem mainDoubleState3_canonical (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.Canonical (fp2At (mainDoubleState3 yst) 2432) := by
  rw [mainDoubleState3, fp2AddFinalState_output _ _ _ _ (by decide)]
  apply fp2AddResult_canonical
  · rw [fp2AddScheduledA_eq_before_out _ _ _ _ (by decide) (by decide),
      mainDoubleState2_y]
    exact hy
  · rw [fp2AddScheduledB_eq_before_out _ _ _ _ (by decide) (by decide),
      mainDoubleState2_y]
    exact hy

theorem mainDoubleState3_toLawful (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.toLawful (fp2At (mainDoubleState3 yst) 2432) =
      2 * Fp2.toLawful (fp2At (mainValidatedState yst) 128) := by
  have hA := fp2AddScheduledA_eq_before_out
    (mainDoubleState2 yst) (2432 : U256) 128 128 (by decide) (by decide)
  have hB := fp2AddScheduledB_eq_before_out
    (mainDoubleState2 yst) (2432 : U256) 128 128 (by decide) (by decide)
  have hinput : Fp2.Canonical (fp2At (mainDoubleState2 yst) 128) := by
    rw [mainDoubleState2_y]
    exact hy
  have hcanonicalA : Fp2.Canonical
      (fp2AddScheduledA (mainDoubleState2 yst) 2432 128 128) :=
    hA.symm ▸ hinput
  have hcanonicalB : Fp2.Canonical
      (fp2AddScheduledB (mainDoubleState2 yst) 2432 128 128) :=
    hB.symm ▸ hinput
  rw [mainDoubleState3, fp2AddFinalState_output _ _ _ _ (by decide),
    fp2AddResult_eq_addSource,
    Fp2.toLawful_addSource hcanonicalA hcanonicalB, hA, hB,
    mainDoubleState2_y]
  ring

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
