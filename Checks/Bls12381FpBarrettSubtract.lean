import Challenge.Bls12381.ProofSupport.FpBarrettSubtract

set_option warningAsError true

namespace Checks.Bls12381FpBarrettSubtract

open Challenge.Bls12381.ProofSupport

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettMultipleLow product).value =
      ((Fp.barrettQuotient product).value *
        EvmSemantics.Crypto.Bls12381.p) %
          Challenge.EvmProof.Limbs.radix ^ 2 :=
  Fp.value_barrettMultipleLow product

example (product : Fp.SchoolbookProduct)
    (hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2) :
    (Fp.barrettRemainder product).value =
      product.value -
        (Fp.barrettQuotient product).value *
          EvmSemantics.Crypto.Bls12381.p :=
  Fp.value_barrettRemainder product hproduct

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettMultipleLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettMultipleLow

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_productLowWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_productLowWords

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettRemainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettRemainder

end Checks.Bls12381FpBarrettSubtract
