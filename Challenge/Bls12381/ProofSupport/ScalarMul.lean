import Challenge.Bls12381.ProofSupport.G1Projective
import Challenge.Bls12381.ProofSupport.G2Projective

set_option warningAsError true

/-! Shared scalar-multiplication refinement boundaries. -/

namespace Challenge.Bls12381.ProofSupport.ScalarMul

open EvmSemantics.Crypto.Bls12381

def fold (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.Point) :
    EvmSemantics.Crypto.Bls12381.Point :=
  EvmSemantics.Crypto.Bls12381.scalarMul scalar point

theorem fold_eq (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.Point) :
    fold scalar point = EvmSemantics.Crypto.Bls12381.scalarMul scalar point := rfl

def foldProjective (scalar : Nat) (point : G1Projective.Point) :
    G1Projective.Point :=
  G1Projective.affine (fold scalar (G1Projective.toAffine point))

@[simp] theorem foldProjective_toAffine (scalar : Nat)
    (point : G1Projective.Point) :
    G1Projective.toAffine (foldProjective scalar point) =
      fold scalar (G1Projective.toAffine point) := by
  simp [foldProjective]

def foldG2 (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    EvmSemantics.Crypto.Bls12381.G2Point :=
  EvmSemantics.Crypto.G2.scalarMul scalar point

def foldG2Projective (scalar : Nat) (point : G2Projective.Point) :
    G2Projective.Point :=
  G2Projective.affine (foldG2 scalar (G2Projective.toAffine point))

@[simp] theorem foldG2Projective_toAffine (scalar : Nat)
    (point : G2Projective.Point) :
    G2Projective.toAffine (foldG2Projective scalar point) =
      foldG2 scalar (G2Projective.toAffine point) := by
  simp [foldG2Projective]

end Challenge.Bls12381.ProofSupport.ScalarMul
