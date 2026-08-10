import Challenge.Bls12381.ProofSupport.Codec
import Challenge.Bls12381.ProofSupport.Fp
import Challenge.Bls12381.ProofSupport.Fp2
import Challenge.Bls12381.ProofSupport.Fp6
import Challenge.Bls12381.ProofSupport.Fp12
import Challenge.Bls12381.ProofSupport.G1Projective
import Challenge.Bls12381.ProofSupport.G2Projective
import Challenge.Bls12381.ProofSupport.ScalarMul
import Challenge.Bls12381.ProofSupport.Msm
import Challenge.Bls12381.ProofSupport.Subgroup

set_option warningAsError true

/-!
# BLS12-381 family proof support

Only facts shared by more than one EIP-2537 challenge belong under this
umbrella. It may depend on generic EVM proof support and the pinned crypto
semantics, but never on an individual challenge.
-/
