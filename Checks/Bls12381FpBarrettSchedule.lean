import Challenge.Bls12381.ProofSupport.FpBarrettSchedule

set_option warningAsError true

namespace Checks.Bls12381FpBarrettSchedule

open Challenge.Bls12381.ProofSupport

example (product : Fp.SchoolbookProduct) :
    Fp.barrettQuotientTop product < Challenge.EvmProof.Limbs.radix :=
  Fp.barrettQuotientTop_lt product

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettQuotient product).q1.toNat =
      Fp.barrettQuotientTop product :=
  Fp.barrettQuotient_q1_value product

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettSchedule_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettSchedule_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettQuotientTop_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettQuotientTop_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettQuotient_q1_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettQuotient_q1_value

end Checks.Bls12381FpBarrettSchedule
