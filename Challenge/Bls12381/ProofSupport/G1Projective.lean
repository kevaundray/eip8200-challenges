import Challenge.Bls12381.ProofSupport.Fp
import Mathlib.Tactic.NormNum

set_option warningAsError true

/-! Projective G1 representation and its affine semantic boundary. -/

namespace Challenge.Bls12381.ProofSupport.G1Projective

open EvmSemantics.Crypto.Bls12381

structure Point where
  x : EvmSemantics.Crypto.Bls12381.Fp
  y : EvmSemantics.Crypto.Bls12381.Fp
  z : EvmSemantics.Crypto.Bls12381.Fp
deriving DecidableEq, Repr

def infinity : Point := { x := 0, y := 1, z := 0 }

def affine : EvmSemantics.Crypto.Bls12381.Point → Point
  | .infinity => infinity
  | .affine x y => { x, y, z := 1 }

def toAffine (point : Point) : EvmSemantics.Crypto.Bls12381.Point :=
  if point.z = 0 then .infinity
  else if point.z = 1 then .affine point.x point.y
  else
    let zInv := point.z⁻¹
    .affine (point.x * zInv ^ 2) (point.y * zInv ^ 3)

@[simp] theorem infinity_toAffine : toAffine infinity = .infinity := by
  simp [toAffine, infinity]

@[simp] theorem affine_toAffine (point : EvmSemantics.Crypto.Bls12381.Point) :
    toAffine (affine point) = point := by
  have hp : EvmSemantics.Crypto.Bls12381.p ≠ 1 := by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  cases point <;> simp [affine, toAffine, infinity, hp]

def add (left right : Point) : Point :=
  affine (EvmSemantics.Crypto.Bls12381.addPoint (toAffine left) (toAffine right))

def double (point : Point) : Point :=
  affine (EvmSemantics.Crypto.Bls12381.doublePoint (toAffine point))

@[simp] theorem add_toAffine (left right : Point) :
    toAffine (add left right) =
      EvmSemantics.Crypto.Bls12381.addPoint (toAffine left) (toAffine right) := by
  simp [add]

@[simp] theorem double_toAffine (point : Point) :
    toAffine (double point) =
      EvmSemantics.Crypto.Bls12381.doublePoint (toAffine point) := by
  simp [double]

end Challenge.Bls12381.ProofSupport.G1Projective
