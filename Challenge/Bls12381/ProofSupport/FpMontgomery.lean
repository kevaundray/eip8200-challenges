import Challenge.Bls12381.ProofSupport.FpSchoolbook

set_option warningAsError true

/-!
# BLS12-381 source-specific Montgomery multiplication

This module models the two-word CIOS `montMul2` routine nested in
`Fp.sol::_modexp`.  The constants and instruction schedule remain separate
from the small base-field representation boundary in `Fp.lean`.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-! ## Constants pinned by `Fp.sol::_modexp.montMul2` -/

/-- The source's `-n₀⁻¹ mod 2²⁵⁶` Montgomery reduction constant. -/
def montgomeryN0Inv : UInt256 := UInt256.ofNat
  0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd

/-- Low word of the source's `R² mod p`, where Montgomery `R = 2⁵¹²`. -/
def montgomeryR2Lo : UInt256 := UInt256.ofNat
  0xcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58

/-- High word of the source's `R² mod p`, where Montgomery `R = 2⁵¹²`. -/
def montgomeryR2Hi : UInt256 := UInt256.ofNat
  0x0010a8c1a49a064ff0a85a3f35446d0b

/-- Natural reconstruction of the two hardcoded `R²` words. -/
def montgomeryR2Value : Nat :=
  montgomeryR2Lo.toNat + Challenge.EvmProof.Limbs.radix * montgomeryR2Hi.toNat

theorem montgomeryN0Inv_value : montgomeryN0Inv.toNat =
    0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd := by
  norm_num [montgomeryN0Inv, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem montgomeryR2Lo_value : montgomeryR2Lo.toNat =
    0xcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58 := by
  norm_num [montgomeryR2Lo, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem montgomeryR2Hi_value : montgomeryR2Hi.toNat =
    0x0010a8c1a49a064ff0a85a3f35446d0b := by
  norm_num [montgomeryR2Hi, Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The hardcoded reduction word really is `-n₀⁻¹` modulo one EVM word. -/
theorem montgomeryN0Inv_spec :
    (montgomeryN0Inv.toNat * modulusLo.toNat) %
        Challenge.EvmProof.Limbs.radix =
      Challenge.EvmProof.Limbs.radix - 1 := by
  norm_num [montgomeryN0Inv, modulusLo,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix]

/-- The two source literals reconstruct `R² mod p` for two-word Montgomery
radix `R = (2²⁵⁶)²`. -/
theorem montgomeryR2_spec : montgomeryR2Value =
    Challenge.EvmProof.Limbs.radix ^ 4 % p := by
  norm_num [montgomeryR2Value, montgomeryR2Lo, montgomeryR2Hi,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix, p, absU]

end Challenge.Bls12381.ProofSupport.Fp
