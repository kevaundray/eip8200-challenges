import Challenge.Bls12381.ProofSupport.FpMontgomeryLowWord

set_option warningAsError true

namespace Checks.Bls12381FpMontgomery

open EvmSemantics.Crypto.Bls12381
open EvmSemantics
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

/-! First CIOS iteration: the source starts from zero and accumulates `x₀*y`. -/

example (x0 y0 y1 : UInt256) :
    Fp.montgomeryAccumulateZero x0 y0 y1 =
      let p0 := Challenge.EvmProof.Limbs.fullMul256 x0 y0
      let p1 := Challenge.EvmProof.Limbs.fullMul256 x0 y1
      let middle := Challenge.EvmProof.Limbs.addTwo256 p1.lo p0.hi
      { t0 := p0.lo
        t1 := middle.word
        t2 := p1.hi + middle.carry : Fp.MontgomeryState } :=
  rfl

example (x0 y0 y1 : UInt256) :
    (Fp.montgomeryAccumulateZero x0 y0 y1).value =
      x0.toNat * (y0.toNat + Challenge.EvmProof.Limbs.radix * y1.toNat) :=
  Fp.montgomeryAccumulateZero_value x0 y0 y1

example (x0 y0 y1 : UInt256) :
    (Fp.montgomeryAccumulateZero x0 y0 y1).t2.toNat <
      Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryAccumulateZero_top_lt x0 y0 y1

/-! Each CIOS reduction chooses `m` so the low word cancels exactly. -/

example (state : Fp.MontgomeryState) :
    Fp.montgomeryReductionMultiplier state =
      state.t0 * Fp.montgomeryN0Inv :=
  rfl

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionMultiplier state).toNat =
      (state.t0.toNat * Fp.montgomeryN0Inv.toNat) %
        Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryReductionMultiplier_value state

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionLowProduct state).lo.toNat =
      ((Fp.montgomeryReductionMultiplier state).toNat *
        Fp.modulusLo.toNat) % Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryReductionLowProduct_lo_value state

example : Fp.montgomeryN0Inv.toNat * Fp.modulusLo.toNat ≡
    Challenge.EvmProof.Limbs.radix - 1
      [MOD Challenge.EvmProof.Limbs.radix] :=
  Fp.montgomeryN0Inv_modEq

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionMultiplier state).toNat * Fp.modulusLo.toNat ≡
      state.t0.toNat * (Challenge.EvmProof.Limbs.radix - 1)
        [MOD Challenge.EvmProof.Limbs.radix] :=
  Fp.montgomeryReductionProduct_modEq state

example (state : Fp.MontgomeryState) :
    state.t0.toNat +
        (Fp.montgomeryReductionMultiplier state).toNat * Fp.modulusLo.toNat ≡ 0
      [MOD Challenge.EvmProof.Limbs.radix] :=
  Fp.montgomeryReductionCancellation_modEq state

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionLowSum state).word = UInt256.ofNat 0 :=
  Fp.montgomeryReductionLowSum_word_eq_zero state

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryN0Inv_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryN0Inv_spec

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryR2_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryR2_spec

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateZero_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateZero_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateZero_top_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateZero_top_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionMultiplier_modEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryReductionMultiplier_modEq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryN0Inv_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryN0Inv_modEq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionProduct_modEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionProduct_modEq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionCancellation_modEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionCancellation_modEq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionLowSum_word_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionLowSum_word_eq_zero

end Checks.Bls12381FpMontgomery
