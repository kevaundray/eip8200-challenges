import Challenge.Bls12381.ProofSupport.G1Projective
import Challenge.Bls12381.ProofSupport.G2Projective

set_option warningAsError true

/-! Shared inversion-free scalar multiplication algorithms. -/

namespace Challenge.Bls12381.ProofSupport.ScalarMul

open EvmSemantics.Crypto.Bls12381

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
