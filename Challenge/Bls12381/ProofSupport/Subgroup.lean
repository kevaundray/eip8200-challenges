import EvmSemantics.Crypto.Bls12381.Curve

set_option warningAsError true

/-!
# BLS12-381 subgroup predicates

EIP-2537 requires prime-order subgroup checks for MSM and pairing inputs, but
not for the two addition precompiles.  Keeping the predicates in the family
support layer prevents the individual challenge specifications from drifting
apart on this security-critical validation rule.
-/

namespace Challenge.Bls12381.ProofSupport.Subgroup

open EvmSemantics.Crypto

/-- Membership in the prime-order G1 subgroup, including infinity. -/
def g1 : Bls12381.Point → Bool
  | .infinity => true
  | point =>
      match Bls12381.scalarMul Bls12381.N point with
      | .infinity => true
      | .affine _ _ => false

/-- Membership in the prime-order G2 subgroup, including infinity. -/
def g2 (point : Bls12381.G2Point) : Bool :=
  G2.inSubgroup Bls12381.N point

@[simp] theorem g1_infinity : g1 (.infinity : Bls12381.Point) = true := rfl

end Challenge.Bls12381.ProofSupport.Subgroup
