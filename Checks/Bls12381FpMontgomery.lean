import Challenge.Bls12381.ProofSupport.FpMontgomery

set_option warningAsError true

namespace Checks.Bls12381FpMontgomery

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

/-! The constants are written literally in `Fp.sol::_modexp.montMul2`. -/

example : Fp.montgomeryN0Inv.toNat =
    0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd :=
  Fp.montgomeryN0Inv_value

example : Fp.montgomeryR2Lo.toNat =
    0xcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58 :=
  Fp.montgomeryR2Lo_value

example : Fp.montgomeryR2Hi.toNat =
    0x0010a8c1a49a064ff0a85a3f35446d0b :=
  Fp.montgomeryR2Hi_value

example :
    (Fp.montgomeryN0Inv.toNat * Fp.modulusLo.toNat) %
        Challenge.EvmProof.Limbs.radix =
      Challenge.EvmProof.Limbs.radix - 1 :=
  Fp.montgomeryN0Inv_spec

example : Fp.montgomeryR2Value =
    Challenge.EvmProof.Limbs.radix ^ 4 % p :=
  Fp.montgomeryR2_spec

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryN0Inv_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryN0Inv_spec

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryR2_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryR2_spec

end Checks.Bls12381FpMontgomery
