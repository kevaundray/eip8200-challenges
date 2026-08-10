import Challenge.Bls12381.ProofSupport.Fp6

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.Fp12

open EvmSemantics.Crypto.Bls12381

structure Repr where
  c0 : Fp6.Repr
  c1 : Fp6.Repr
deriving DecidableEq

def toField (a : Repr) : EvmSemantics.Crypto.Bls12381.Fp12 :=
  { c0 := Fp6.toField a.c0, c1 := Fp6.toField a.c1 }

def ofField (a : EvmSemantics.Crypto.Bls12381.Fp12) : Repr :=
  { c0 := Fp6.ofField a.c0, c1 := Fp6.ofField a.c1 }

def Refines (a : Repr) (value : EvmSemantics.Crypto.Bls12381.Fp12) : Prop :=
  toField a = value

@[simp] theorem toField_ofField (a : EvmSemantics.Crypto.Bls12381.Fp12) :
    toField (ofField a) = a := by
  cases a
  simp [toField, ofField]

theorem refines_ofField (a : EvmSemantics.Crypto.Bls12381.Fp12) :
    Refines (ofField a) a := by
  simp [Refines]

/-- Three-multiplication Karatsuba formula for the quadratic extension. -/
def mul (a b : Repr) : Repr :=
  let v0 := Fp6.mul a.c0 b.c0
  let v1 := Fp6.mul a.c1 b.c1
  let t := Fp6.mul (Fp6.add a.c0 a.c1) (Fp6.add b.c0 b.c1)
  { c0 := Fp6.add v0 (Fp6.mulByV v1)
    c1 := Fp6.sub (Fp6.sub t v0) v1 }

/-- Complex squaring using two Fp6 multiplications. -/
def square (a : Repr) : Repr :=
  let ab := Fp6.mul a.c0 a.c1
  let t := Fp6.mul (Fp6.add a.c0 a.c1)
    (Fp6.add a.c0 (Fp6.mulByV a.c1))
  { c0 := Fp6.sub (Fp6.sub t ab) (Fp6.mulByV ab)
    c1 := Fp6.add ab ab }
def conj (a : Repr) : Repr := ofField (_root_.Fp12.conj (toField a))
def inv (a : Repr) : Repr := ofField (toField a)⁻¹

theorem mul_components (a b : Repr) :
    mul a b =
      let v0 := Fp6.mul a.c0 b.c0
      let v1 := Fp6.mul a.c1 b.c1
      let t := Fp6.mul (Fp6.add a.c0 a.c1) (Fp6.add b.c0 b.c1)
      { c0 := Fp6.add v0 (Fp6.mulByV v1)
        c1 := Fp6.sub (Fp6.sub t v0) v1 } := rfl

theorem refines_mul (a b : Repr) : Refines (mul a b) (toField a * toField b) := by
  change toField (mul a b) = _root_.Fp12.mul (toField a) (toField b)
  simp [mul, toField, _root_.Fp12.mul]
theorem refines_square (a : Repr) :
    Refines (square a) (_root_.Fp12.square (toField a)) := by
  change toField (square a) = _root_.Fp12.square (toField a)
  simp [square, toField, _root_.Fp12.square]
theorem refines_conj (a : Repr) :
    Refines (conj a) (_root_.Fp12.conj (toField a)) :=
  refines_ofField _
theorem refines_inv (a : Repr) : Refines (inv a) (toField a)⁻¹ :=
  refines_ofField _

end Challenge.Bls12381.ProofSupport.Fp12
