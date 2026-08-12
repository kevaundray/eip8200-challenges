import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulRight

set_option warningAsError true

/-! # Low-memory lawful endpoint for frozen G2ADD Fp2 products -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2MulFinalState_canonical_of_low (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2MulFinalState yst out a b) out) := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_low yst a b haEnd haLow
  have hrightInput := fp2MulRightInput_eq_fp2At_of_low yst a b hbEnd hbLow
  apply fp2MulFinalState_canonical yst out a b
  · rwa [hleftInput]
  · rwa [hrightInput]
  · exact fp2MulScheduledLeft_eq_of_low yst out a b haEnd haLow
      houtHigh (by omega)
  · exact fp2MulScheduledRight_eq_of_low yst out a b hbEnd hbLow
      houtHigh (by omega)
  · exact houtHigh
  · exact hout

theorem fp2MulFinalState_toLawful_mul_of_low (yst : EvmState)
    (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2MulFinalState yst out a b) out) =
      Fp2.toLawful (fp2At yst a) * Fp2.toLawful (fp2At yst b) := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_low yst a b haEnd haLow
  have hrightInput := fp2MulRightInput_eq_fp2At_of_low yst a b hbEnd hbLow
  rw [← hleftInput, ← hrightInput]
  exact fp2MulFinalState_toLawful_mul yst out a b
    (hleftInput.symm ▸ ha) (hrightInput.symm ▸ hb)
    (fp2MulScheduledLeft_eq_of_low yst out a b haEnd haLow
      houtHigh (by omega))
    (fp2MulScheduledRight_eq_of_low yst out a b hbEnd hbLow
      houtHigh (by omega)) houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
