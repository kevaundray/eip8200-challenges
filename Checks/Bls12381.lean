import Challenge.Bls12381
import Checks.Bls12381FpRepresentation
import Checks.Bls12381FpAddSubSchedule
import Checks.Bls12381FpAdd
import Checks.Bls12381FpAddSub
import Checks.Bls12381FpNeg
import Checks.Bls12381FpAddSubLawful
import Checks.Bls12381FpBarrettSchedule
import Checks.Bls12381FpBarrett
import Checks.Bls12381FpBarrettSubtract
import Checks.Bls12381FpBarrettReduce
import Checks.Bls12381FpMul
import Checks.Bls12381FpMontgomery
import Checks.Bls12381FpMontgomeryPow
import Checks.Bls12381FpInvConstants
import Checks.Bls12381FpInv

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
#print axioms Challenge.Bls12381.ProofSupport.ScalarMul.loopG1_step
#print axioms Challenge.Bls12381.ProofSupport.ScalarMul.loopG2_step
#print axioms Challenge.Bls12381.ProofSupport.Msm.foldG1_append
#print axioms Challenge.Bls12381.ProofSupport.Msm.foldG2_append
