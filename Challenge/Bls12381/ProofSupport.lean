import Challenge.Bls12381.ProofSupport.Codec
import Challenge.Bls12381.ProofSupport.Fp
import Challenge.Bls12381.ProofSupport.FpConstants
import Challenge.Bls12381.ProofSupport.FpAddSub
import Challenge.Bls12381.ProofSupport.FpAddSubLawful
import Challenge.Bls12381.ProofSupport.FpSchoolbook
import Challenge.Bls12381.ProofSupport.FpBarrettSchedule
import Challenge.Bls12381.ProofSupport.FpBarrett
import Challenge.Bls12381.ProofSupport.FpBarrettSubtract
import Challenge.Bls12381.ProofSupport.FpBarrettReduce
import Challenge.Bls12381.ProofSupport.FpMul
import Challenge.Bls12381.ProofSupport.FpSquare
import Challenge.Bls12381.ProofSupport.FpMontgomeryLawful
import Challenge.Bls12381.ProofSupport.FpMontgomeryPowLawful
import Challenge.Bls12381.ProofSupport.FpInvConstants
import Challenge.Bls12381.ProofSupport.FpInv
import Challenge.Bls12381.ProofSupport.LawfulFp2
import Challenge.Bls12381.ProofSupport.Fp2
import Challenge.Bls12381.ProofSupport.LawfulFp6
import Challenge.Bls12381.ProofSupport.LawfulFp6Norm
import Challenge.Bls12381.ProofSupport.Fp6
import Challenge.Bls12381.ProofSupport.LawfulFp12
import Challenge.Bls12381.ProofSupport.LawfulFp12Norm
import Challenge.Bls12381.ProofSupport.Fp12
import Challenge.Bls12381.ProofSupport.G1Projective
import Challenge.Bls12381.ProofSupport.G2Projective
import Challenge.Bls12381.ProofSupport.ScalarMul
import Challenge.Bls12381.ProofSupport.Msm
import Challenge.Bls12381.ProofSupport.PrimeField
import Challenge.Bls12381.ProofSupport.PrimeCertificate
import Challenge.Bls12381.ProofSupport.Subgroup

set_option warningAsError true

/-!
# BLS12-381 family proof support

Only facts shared by more than one EIP-2537 challenge belong under this
umbrella. It may depend on generic EVM proof support and the pinned crypto
semantics, but never on an individual challenge.
-/
