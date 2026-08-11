import Challenge.Bls12381.ProofSupport.Fp2SqrtRefinement

set_option warningAsError true

namespace Checks.Bls12381Fp2SqrtRefinement

open Challenge.Bls12381.ProofSupport

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    (Fp2.sqrtSource a).exists_ =
        (Fp2.SqrtProgram.run Fp2.lawfulSqrtOps (Fp2.toLawful a)).exists_ ∧
      Fp2.SqrtPairRel (Fp2.sqrtSource a).root
        (Fp2.SqrtProgram.run Fp2.lawfulSqrtOps (Fp2.toLawful a)).root :=
  Fp2.sqrtSource_refines_lawful ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtSourceOps_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtSourceOps_refines

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtSource_refines_lawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtSource_refines_lawful

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_zero_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_zero_repr

end Checks.Bls12381Fp2SqrtRefinement
