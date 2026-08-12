import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainDoubleSquare
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddInputs

set_option warningAsError true

/-! # Lawful numerator phases of frozen G2ADD doubling -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem mainDoubleState1_xsq (yst : EvmState) :
    fp2At (mainDoubleState1 yst) 2176 = fp2At (mainDoubleState0 yst) 2176 := by
  unfold mainDoubleState1
  exact fp2AddFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)

theorem mainDoubleState1_canonical (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.Canonical (fp2At (mainDoubleState1 yst) 2304) := by
  rw [mainDoubleState1, fp2AddFinalState_output _ _ _ _ (by decide)]
  apply fp2AddResult_canonical
  · rw [fp2AddScheduledA_eq_before_out _ _ _ _ (by decide) (by decide)]
    exact mainDoubleState0_canonical yst hx
  · rw [fp2AddScheduledB_eq_before_out _ _ _ _ (by decide) (by decide)]
    exact mainDoubleState0_canonical yst hx

theorem mainDoubleState1_toLawful (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.toLawful (fp2At (mainDoubleState1 yst) 2304) =
      2 * Fp2.toLawful (fp2At (mainValidatedState yst) 0) ^ 2 := by
  have hcanonical := mainDoubleState0_canonical yst hx
  have hA := fp2AddScheduledA_eq_before_out
    (mainDoubleState0 yst) (2304 : U256) 2176 2176 (by decide) (by decide)
  have hB := fp2AddScheduledB_eq_before_out
    (mainDoubleState0 yst) (2304 : U256) 2176 2176 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2AddScheduledA (mainDoubleState0 yst) 2304 2176 2176) :=
    hA.symm ▸ hcanonical
  have hcanonicalB : Fp2.Canonical
      (fp2AddScheduledB (mainDoubleState0 yst) 2304 2176 2176) :=
    hB.symm ▸ hcanonical
  rw [mainDoubleState1, fp2AddFinalState_output _ _ _ _ (by decide),
    fp2AddResult_eq_addSource,
    Fp2.toLawful_addSource hcanonicalA hcanonicalB, hA, hB,
    mainDoubleState0_toLawful yst hx]
  ring

private theorem mainDoubleState2_xsq (yst : EvmState) :
    fp2At (mainDoubleState2 yst) 2176 = fp2At (mainDoubleState0 yst) 2176 := by
  unfold mainDoubleState2
  exact (fp2AddFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainDoubleState1_xsq yst)

theorem mainDoubleState2_canonical (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.Canonical (fp2At (mainDoubleState2 yst) 2304) := by
  rw [mainDoubleState2, fp2AddFinalState_output _ _ _ _ (by decide)]
  apply fp2AddResult_canonical
  · rw [fp2AddScheduledA_eq_at_out _ _ _ (by decide)]
    exact mainDoubleState1_canonical yst hx
  · rw [fp2AddScheduledB_eq_before_out _ _ _ _ (by decide) (by decide),
      mainDoubleState1_xsq]
    exact mainDoubleState0_canonical yst hx

theorem mainDoubleState2_toLawful (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.toLawful (fp2At (mainDoubleState2 yst) 2304) =
      3 * Fp2.toLawful (fp2At (mainValidatedState yst) 0) ^ 2 := by
  have hnum := mainDoubleState1_canonical yst hx
  have hsq := mainDoubleState0_canonical yst hx
  have hA := fp2AddScheduledA_eq_at_out
    (mainDoubleState1 yst) (2304 : U256) 2176 (by decide)
  have hB := fp2AddScheduledB_eq_before_out
    (mainDoubleState1 yst) (2304 : U256) 2304 2176 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2AddScheduledA (mainDoubleState1 yst) 2304 2304 2176) :=
    hA.symm ▸ hnum
  have hcanonicalB : Fp2.Canonical
      (fp2AddScheduledB (mainDoubleState1 yst) 2304 2304 2176) := by
    rw [hB, mainDoubleState1_xsq]
    exact hsq
  rw [mainDoubleState2, fp2AddFinalState_output _ _ _ _ (by decide),
    fp2AddResult_eq_addSource,
    Fp2.toLawful_addSource hcanonicalA hcanonicalB, hA, hB,
    mainDoubleState1_toLawful yst hx, mainDoubleState1_xsq,
    mainDoubleState0_toLawful yst hx]
  ring

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
