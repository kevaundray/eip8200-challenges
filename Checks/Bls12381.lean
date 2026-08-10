import Challenge.Bls12381

set_option warningAsError true

/-!
# Shared BLS12-381 proof-support checks

This target keeps the family-level support independently buildable. Individual
challenge correctness theorems have their own axiom-footprint checks.
-/

#print axioms Challenge.Bls12381.ProofSupport.Codec.decodeFp_encodeFp

#print axioms Challenge.Bls12381.ProofSupport.Fp.value_ofField
#print axioms Challenge.Bls12381.ProofSupport.Fp.value_normalize
#print axioms Challenge.Bls12381.ProofSupport.Fp.refines_add
#print axioms Challenge.Bls12381.ProofSupport.Fp2.mul_components
#print axioms Challenge.Bls12381.ProofSupport.Fp2.refines_mul
#print axioms Challenge.Bls12381.ProofSupport.Fp6.mul_components
#print axioms Challenge.Bls12381.ProofSupport.Fp6.refines_mul
#print axioms Challenge.Bls12381.ProofSupport.Fp12.mul_components
#print axioms Challenge.Bls12381.ProofSupport.Fp12.refines_mul
#print axioms Challenge.Bls12381.ProofSupport.G1Projective.affine_toAffine
#print axioms Challenge.Bls12381.ProofSupport.G2Projective.affine_toAffine
#print axioms Challenge.Bls12381.ProofSupport.ScalarMul.fold_eq
#print axioms Challenge.Bls12381.ProofSupport.Msm.fold_append
