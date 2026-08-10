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

def add (a b : Repr) : Repr :=
  { c0 := Fp6.add a.c0 b.c0, c1 := Fp6.add a.c1 b.c1 }

def sub (a b : Repr) : Repr :=
  { c0 := Fp6.sub a.c0 b.c0, c1 := Fp6.sub a.c1 b.c1 }

def neg (a : Repr) : Repr :=
  { c0 := Fp6.neg a.c0, c1 := Fp6.neg a.c1 }

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

/-- Component implementation of the Fp12 conjugation map. -/
def conj (a : Repr) : Repr := { c0 := a.c0, c1 := Fp6.neg a.c1 }

/-- The Fp6 norm `c0² - v·c1²` used by Fp12 inversion. -/
def invNorm (a : Repr) : Fp6.Repr :=
  Fp6.sub (Fp6.square a.c0) (Fp6.mulByV (Fp6.square a.c1))

/-- Actual quadratic-extension inverse parameterized by an Fp6 inversion primitive. -/
def invWith (invert : Fp6.Repr → Fp6.Repr) (a : Repr) : Repr :=
  let normInv := invert (invNorm a)
  { c0 := Fp6.mul a.c0 normInv
    c1 := Fp6.neg (Fp6.mul a.c1 normInv) }

/-- Specification adapter; not an executable implementation boundary. -/
def invSpecRepr (a : Repr) : Repr := ofField (_root_.Fp12.inv (toField a))

/-- Component Frobenius formula parameterized by the BLS12-381 gamma constants. -/
def frobenius (gammaW gammaV gammaV2 : Fp2.Repr) (a : Repr) : Repr :=
  let frob6 (x : Fp6.Repr) : Fp6.Repr :=
    { c0 := Fp2.conj x.c0
      c1 := Fp2.mul gammaV (Fp2.conj x.c1)
      c2 := Fp2.mul gammaV2 (Fp2.conj x.c2) }
  { c0 := frob6 a.c0
    c1 := Fp6.mulByFp2 (frob6 a.c1) gammaW }

/-- Sparse multiplication by a Miller-loop line element. -/
def mulBy014 (a : Repr) (b0 b1 b4 : Fp2.Repr) : Repr :=
  let a0b0 := Fp6.mulByFp2 a.c0 b0
  let a1b1 := Fp6.mulBy01 a.c1 b1 b4
  let sum := Fp6.mulBy01 (Fp6.add a.c0 a.c1) (Fp2.add b0 b1) b4
  { c0 := Fp6.add a0b0 (Fp6.mulByV a1b1)
    c1 := Fp6.sub (Fp6.sub sum a0b0) a1b1 }

/-- The current executable cyclotomic square uses the proven general square formula. -/
def cyclotomicSquare (a : Repr) : Repr := square a

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
theorem refines_add (a b : Repr) : Refines (add a b) (toField a + toField b) := by
  change toField (add a b) = _root_.Fp12.add (toField a) (toField b)
  simp [add, toField, _root_.Fp12.add]
theorem refines_sub (a b : Repr) : Refines (sub a b) (toField a - toField b) := by
  change toField (sub a b) = _root_.Fp12.sub (toField a) (toField b)
  simp [sub, toField, _root_.Fp12.sub]
theorem refines_neg (a : Repr) : Refines (neg a) (-toField a) := by
  change toField (neg a) = _root_.Fp12.neg (toField a)
  simp [neg, toField, _root_.Fp12.neg]
theorem refines_conj (a : Repr) :
    Refines (conj a) (_root_.Fp12.conj (toField a)) := by
  simp [Refines, conj, toField, _root_.Fp12.conj]
theorem refines_frobenius (gammaW gammaV gammaV2 : Fp2.Repr) (a : Repr) :
    Refines (frobenius gammaW gammaV gammaV2 a)
      (_root_.Fp12.frobenius (Fp2.toField gammaW) (Fp2.toField gammaV)
        (Fp2.toField gammaV2) (toField a)) := by
  let frob6 (x : Fp6.Repr) : Fp6.Repr :=
    { c0 := Fp2.conj x.c0
      c1 := Fp2.mul gammaV (Fp2.conj x.c1)
      c2 := Fp2.mul gammaV2 (Fp2.conj x.c2) }
  have hfrob6 (x : Fp6.Repr) : Fp6.toField (frob6 x) =
      { c0 := _root_.Fp2.conj (Fp2.toField x.c0)
        c1 := Fp2.toField gammaV * _root_.Fp2.conj (Fp2.toField x.c1)
        c2 := Fp2.toField gammaV2 * _root_.Fp2.conj (Fp2.toField x.c2) } := by
    simp [frob6, Fp6.toField]
  change toField (frobenius gammaW gammaV gammaV2 a) = _
  simp only [frobenius, toField, _root_.Fp12.frobenius]
  rw [hfrob6 a.c0, Fp6.toField_mulByFp2, hfrob6 a.c1]
  rfl
theorem refines_mulBy014 (a : Repr) (b0 b1 b4 : Fp2.Repr) :
    Refines (mulBy014 a b0 b1 b4)
      (_root_.Fp12.mulBy014 (toField a) (Fp2.toField b0)
        (Fp2.toField b1) (Fp2.toField b4)) := by
  change toField (mulBy014 a b0 b1 b4) = _
  simp [mulBy014, toField, _root_.Fp12.mulBy014]
theorem refines_invWith (invert : Fp6.Repr → Fp6.Repr) (a : Repr)
    (hinvert : Fp6.toField (invert (invNorm a)) =
      _root_.Fp6.inv (Fp6.toField (invNorm a))) :
    Refines (invWith invert a) (_root_.Fp12.inv (toField a)) := by
  let n := invNorm a
  have hn : Fp6.toField n =
      _root_.Fp6.square (Fp6.toField a.c0) -
        _root_.Fp6.mulByV (_root_.Fp6.square (Fp6.toField a.c1)) := by
    simp [n, invNorm]
  have hinvert' : Fp6.toField (invert n) = _root_.Fp6.inv (Fp6.toField n) := by
    simpa [n] using hinvert
  change toField (invWith invert a) = _root_.Fp12.inv (toField a)
  change
    ({ c0 := Fp6.toField (Fp6.mul a.c0 (invert n))
       c1 := Fp6.toField (Fp6.neg (Fp6.mul a.c1 (invert n))) } :
      EvmSemantics.Crypto.Bls12381.Fp12) = _
  simp only [Fp6.toField_mul, Fp6.toField_neg, _root_.Fp12.inv, toField]
  rw [hinvert', hn]
  simp only [Fp6.semantic_pow_two]
theorem refines_invSpecRepr (a : Repr) :
    Refines (invSpecRepr a) (_root_.Fp12.inv (toField a)) := refines_ofField _

@[simp] theorem toField_add (a b : Repr) :
    toField (add a b) = toField a + toField b := refines_add a b
@[simp] theorem toField_sub (a b : Repr) :
    toField (sub a b) = toField a - toField b := refines_sub a b
@[simp] theorem toField_neg (a : Repr) :
    toField (neg a) = -toField a := refines_neg a
@[simp] theorem toField_mul (a b : Repr) :
    toField (mul a b) = toField a * toField b := refines_mul a b
@[simp] theorem toField_square (a : Repr) :
    toField (square a) = _root_.Fp12.square (toField a) := refines_square a
@[simp] theorem toField_conj (a : Repr) :
    toField (conj a) = _root_.Fp12.conj (toField a) := refines_conj a
@[simp] theorem toField_frobenius (gammaW gammaV gammaV2 : Fp2.Repr) (a : Repr) :
    toField (frobenius gammaW gammaV gammaV2 a) =
      _root_.Fp12.frobenius (Fp2.toField gammaW) (Fp2.toField gammaV)
        (Fp2.toField gammaV2) (toField a) :=
  refines_frobenius gammaW gammaV gammaV2 a
@[simp] theorem toField_mulBy014 (a : Repr) (b0 b1 b4 : Fp2.Repr) :
    toField (mulBy014 a b0 b1 b4) =
      _root_.Fp12.mulBy014 (toField a) (Fp2.toField b0)
        (Fp2.toField b1) (Fp2.toField b4) :=
  refines_mulBy014 a b0 b1 b4
@[simp] theorem toField_invWith (invert : Fp6.Repr → Fp6.Repr) (a : Repr)
    (hinvert : Fp6.toField (invert (invNorm a)) =
      _root_.Fp6.inv (Fp6.toField (invNorm a))) :
    toField (invWith invert a) = _root_.Fp12.inv (toField a) :=
  refines_invWith invert a hinvert

end Challenge.Bls12381.ProofSupport.Fp12
