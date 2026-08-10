import Challenge.Bls12381.ProofSupport.Fp

set_option warningAsError true

namespace Checks.Bls12381Fp

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (n : Nat) : Fp.Canonical (Fp.normalize n) :=
  Fp.canonical_normalize n

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.addCanonical a b) = (Fp.value a + Fp.value b) % p :=
  Fp.value_addCanonical ha hb

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.subCanonical a b) = (p + Fp.value a - Fp.value b) % p :=
  Fp.value_subCanonical ha hb

example (a b : Fp.Limbs) :
    Fp.toField (Fp.mul a b) = Fp.toField a * Fp.toField b :=
  Fp.toField_mul a b

example (a : Fp.Limbs) (exponent : Nat) :
    Fp.toField (Fp.powSpecRepr a exponent) = Fp.PowSpec a exponent :=
  Fp.toField_powSpecRepr a exponent

#print axioms Fp.value_addCanonical
#print axioms Fp.value_subCanonical
#print axioms Fp.toField_mul
#print axioms Fp.toField_powSpecRepr

end Checks.Bls12381Fp
