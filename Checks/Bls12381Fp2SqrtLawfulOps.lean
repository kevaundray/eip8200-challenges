import Challenge.Bls12381.ProofSupport.Fp2SqrtLawfulOps

set_option warningAsError true

namespace Checks.Bls12381Fp2SqrtLawfulOps

open Challenge.Bls12381.ProofSupport

example (x : LawfulFp2.Base) :
    Fp2.lawfulSqrt x =
      x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) :=
  Fp2.lawfulSqrt_eq x

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulSqrt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulSqrt_eq

end Checks.Bls12381Fp2SqrtLawfulOps
