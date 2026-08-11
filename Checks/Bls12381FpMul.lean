import Challenge.Bls12381.ProofSupport.FpMul

set_option warningAsError true

namespace Checks.Bls12381FpMul

open Challenge.Bls12381.ProofSupport

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.mulCanonical a b) =
      (Fp.value a * Fp.value b) % EvmSemantics.Crypto.Bls12381.p :=
  Fp.value_mulCanonical ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Fp.mulCanonical a b) :=
  Fp.canonical_mulCanonical ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.toField (Fp.mulCanonical a b) = Fp.toField a * Fp.toField b :=
  Fp.toField_mulCanonical ha hb

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_mulCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_mulCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.refines_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.refines_mulCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toField_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toField_mulCanonical

end Checks.Bls12381FpMul
