import Challenge.Bls12381.ProofSupport.G1Projective
import Challenge.Bls12381.ProofSupport.G2Projective

set_option warningAsError true

/-! Shared inversion-free scalar multiplication algorithms. -/

namespace Challenge.Bls12381.ProofSupport.ScalarMul

open EvmSemantics.Crypto.Bls12381

/-! ## Transparent binary scalar semantics -/

/-- Proof-friendly right-to-left binary double-and-add.  This transparent
recursion is the local mathematical scalar operation; no equality to the
pinned inverse-dependent curve scalar multiplication is claimed. -/
def binary {Point : Type} (zero : Point) (add : Point → Point → Point)
    (double : Point → Point) (scalar : Nat) (point : Point) : Point :=
  if hzero : scalar = 0 then zero
  else
    let rest := binary zero add double (scalar / 2) (double point)
    if scalar % 2 = 1 then add rest point else rest
termination_by scalar
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero hzero) (by omega)

@[simp] theorem binary_zero {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    binary zero add double 0 point = zero := by
  rw [binary]
  simp

theorem binary_step {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) (hscalar : scalar ≠ 0) :
    binary zero add double scalar point =
      if scalar % 2 = 1 then
        add (binary zero add double (scalar / 2) (double point)) point
      else binary zero add double (scalar / 2) (double point) := by
  rw [binary]
  simp [hscalar]

theorem binary_even {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) :
    binary zero add double (2 * scalar) point =
      binary zero add double scalar (double point) := by
  cases scalar with
  | zero => simp
  | succ scalar =>
      rw [binary_step]
      · norm_num
      · omega

theorem binary_odd {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) :
    binary zero add double (2 * scalar + 1) point =
      add (binary zero add double scalar (double point)) point := by
  rw [binary_step]
  · rw [show (2 * scalar + 1) / 2 = scalar by omega]
    norm_num
  · omega

/-- Binary scalar multiplication preserves any invariant preserved by the
identity, addition, and doubling operations. -/
theorem binary_preserves {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (Valid : Point → Prop)
    (hzero : Valid zero)
    (hadd : ∀ left right, Valid left → Valid right → Valid (add left right))
    (hdouble : ∀ point, Valid point → Valid (double point))
    (scalar : Nat) (point : Point) (hpoint : Valid point) :
    Valid (binary zero add double scalar point) := by
  induction scalar using Nat.strong_induction_on generalizing point with
  | h scalar ih =>
      by_cases hscalar : scalar = 0
      · subst scalar
        simpa using hzero
      · rw [binary_step zero add double scalar point hscalar]
        have hhalf : scalar / 2 < scalar :=
          Nat.div_lt_self (Nat.zero_lt_of_ne_zero hscalar) (by omega)
        have hrest :
            Valid (binary zero add double (scalar / 2) (double point)) :=
          ih (scalar / 2) hhalf (double point) (hdouble point hpoint)
        by_cases hodd : scalar % 2 = 1
        · rw [if_pos hodd]
          exact hadd _ _ hrest hpoint
        · rw [if_neg hodd]
          exact hrest

/-- Right-to-left binary G1 scalar multiplication. `fuel` is a structural
termination argument; the public entry supplies the scalar itself, while the
working scalar is halved on every nonterminal iteration. -/
def loopG1 : Nat → Nat → G1Projective.Point → G1Projective.Point →
    G1Projective.Point
  | 0, _, acc, _ => acc
  | fuel + 1, scalar, acc, base =>
      if scalar = 0 then acc
      else
        let acc' := if scalar % 2 = 1 then G1Projective.add acc base else acc
        loopG1 fuel (scalar / 2) acc' (G1Projective.double base)

def g1 (scalar : Nat) (point : G1Projective.Point) : G1Projective.Point :=
  loopG1 scalar scalar G1Projective.infinity point

/-- Right-to-left binary G2 scalar multiplication. -/
def loopG2 : Nat → Nat → G2Projective.Point → G2Projective.Point →
    G2Projective.Point
  | 0, _, acc, _ => acc
  | fuel + 1, scalar, acc, base =>
      if scalar = 0 then acc
      else
        let acc' := if scalar % 2 = 1 then G2Projective.add acc base else acc
        loopG2 fuel (scalar / 2) acc' (G2Projective.double base)

def g2 (scalar : Nat) (point : G2Projective.Point) : G2Projective.Point :=
  loopG2 scalar scalar G2Projective.infinity point

/-- Pinned affine specifications, kept separate from the executable
projective algorithms. -/
def g1Spec (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.Point) :
    EvmSemantics.Crypto.Bls12381.Point :=
  EvmSemantics.Crypto.Bls12381.scalarMul scalar point

def g2Spec (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    EvmSemantics.Crypto.Bls12381.G2Point :=
  EvmSemantics.Crypto.G2.scalarMul scalar point

@[simp] theorem g1_zero (point : G1Projective.Point) :
    g1 0 point = G1Projective.infinity := rfl

@[simp] theorem g2_zero (point : G2Projective.Point) :
    g2 0 point = G2Projective.infinity := rfl

@[simp] theorem g1_one (point : G1Projective.Point) : g1 1 point = point := by
  simp [g1, loopG1]

@[simp] theorem g2_one (point : G2Projective.Point) : g2 1 point = point := by
  simp [g2, loopG2]

theorem loopG1_step (fuel scalar : Nat) (acc base : G1Projective.Point)
    (hscalar : scalar ≠ 0) :
    loopG1 (fuel + 1) scalar acc base =
      loopG1 fuel (scalar / 2)
        (if scalar % 2 = 1 then G1Projective.add acc base else acc)
        (G1Projective.double base) := by
  simp [loopG1, hscalar]

theorem loopG2_step (fuel scalar : Nat) (acc base : G2Projective.Point)
    (hscalar : scalar ≠ 0) :
    loopG2 (fuel + 1) scalar acc base =
      loopG2 fuel (scalar / 2)
        (if scalar % 2 = 1 then G2Projective.add acc base else acc)
        (G2Projective.double base) := by
  simp [loopG2, hscalar]

end Challenge.Bls12381.ProofSupport.ScalarMul
