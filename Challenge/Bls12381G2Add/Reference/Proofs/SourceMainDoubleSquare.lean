import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulLawful

set_option warningAsError true

/-! # Lawful x-square phase of frozen G2ADD doubling -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainDoubleState0_canonical (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.Canonical (fp2At (mainDoubleState0 yst) 2176) := by
  unfold mainDoubleState0
  apply fp2MulFinalState_canonical_of_low
  · rwa [mainAfterDoubleYZero_fp2At]
  · rwa [mainAfterDoubleYZero_fp2At]
  all_goals decide

theorem mainDoubleState0_toLawful (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.toLawful (fp2At (mainDoubleState0 yst) 2176) =
      Fp2.toLawful (fp2At (mainValidatedState yst) 0) ^ 2 := by
  have h := fp2MulFinalState_toLawful_mul_of_low
    (mainAfterDoubleYZero yst) (2176 : U256) 0 0
    (by rwa [mainAfterDoubleYZero_fp2At])
    (by rwa [mainAfterDoubleYZero_fp2At])
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rw [mainAfterDoubleYZero_fp2At] at h
  simpa only [mainDoubleState0, pow_two] using h

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
