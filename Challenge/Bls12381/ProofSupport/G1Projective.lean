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

/-- Jacobian doubling for the `a = 0` BLS12-381 G1 curve.  The `y = 0`
branch is the vertical tangent and therefore returns infinity explicitly. -/
def double (point : Point) : Point :=
  if point.z = 0 ∨ point.y = 0 then infinity
  else
    let a := point.x ^ 2
    let b := point.y ^ 2
    let c := b ^ 2
    let d := 2 * ((point.x + b) ^ 2 - a - c)
    let e := 3 * a
    let f := e ^ 2
    { x := f - 2 * d
      y := e * (d - (f - 2 * d)) - 8 * c
      z := 2 * point.y * point.z }

/-- Standard Jacobian addition, including both infinity branches, the inverse
pair, and the equal-point/doubling branch.  It performs no affine conversion
or field inversion. -/
def add (left right : Point) : Point :=
  if left.z = 0 then right
  else if right.z = 0 then left
  else
    let z1z1 := left.z ^ 2
    let z2z2 := right.z ^ 2
    let u1 := left.x * z2z2
    let u2 := right.x * z1z1
    let s1 := left.y * right.z * z2z2
    let s2 := right.y * left.z * z1z1
    if u1 = u2 then
      if s1 = s2 then double left else infinity
    else
      let h := u2 - u1
      let i := (2 * h) ^ 2
      let j := h * i
      let r := 2 * (s2 - s1)
      let v := u1 * i
      { x := r ^ 2 - j - 2 * v
        y := r * (v - (r ^ 2 - j - 2 * v)) - 2 * s1 * j
        z := ((left.z + right.z) ^ 2 - z1z1 - z2z2) * h }

@[simp] theorem double_infinity : double infinity = infinity := by
  simp [double, infinity]

@[simp] theorem double_of_z_eq_zero (point : Point) (hz : point.z = 0) :
    double point = infinity := by
  simp [double, hz]

@[simp] theorem double_of_y_eq_zero (point : Point) (hy : point.y = 0) :
    double point = infinity := by
  simp [double, hy]

@[simp] theorem infinity_add (point : Point) : add infinity point = point := by
  simp [add, infinity]

@[simp] theorem add_infinity_of_z_ne_zero (point : Point) (hz : point.z ≠ 0) :
    add point infinity = point := by
  simp [add, infinity, hz]

@[simp] theorem add_infinity_of_z_eq_zero (point : Point) (hz : point.z = 0) :
    add point infinity = infinity := by
  simp [add, infinity, hz]

/-- The affine semantic bridge requires a cancellation theorem for the pinned
`Fin p` inverse.  Keeping that dependency explicit prevents the projective
algorithm from silently calling the semantic affine operation. -/
def InverseLaw : Prop :=
  ∀ a : EvmSemantics.Crypto.Bls12381.Fp, a ≠ 0 → a * a⁻¹ = 1

end Challenge.Bls12381.ProofSupport.G1Projective
