import Challenge.Bls12381.ProofSupport.FpBarrett

set_option warningAsError true

namespace Checks.Bls12381FpBarrett

open Challenge.Bls12381.ProofSupport

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettQuotient product).value =
      ((product.r1.toNat + Challenge.EvmProof.Limbs.radix *
          product.r2.toNat) * Fp.barrettMu) /
        Challenge.EvmProof.Limbs.radix ^ 3 :=
  Fp.value_barrettQuotient product

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettLower_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettLower_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettSchedule_regroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettSchedule_regroup

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettSchedule_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettSchedule_div

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettQuotient_value_eq_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettQuotient_value_eq_schedule

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettQuotient

end Checks.Bls12381FpBarrett
