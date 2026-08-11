import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

namespace Checks.Bls12381ScalarMul

open Challenge.Bls12381.ProofSupport

variable {P : Type} (zero : P) (add : P → P → P) (double : P → P)

example (point : P) : ScalarMul.binary zero add double 0 point = zero :=
  ScalarMul.binary_zero zero add double point

example (scalar : Nat) (point : P) :
    ScalarMul.binary zero add double (2 * scalar) point =
      ScalarMul.binary zero add double scalar (double point) :=
  ScalarMul.binary_even zero add double scalar point

example (scalar : Nat) (point : P) :
    ScalarMul.binary zero add double (2 * scalar + 1) point =
      add (ScalarMul.binary zero add double scalar (double point)) point :=
  ScalarMul.binary_odd zero add double scalar point

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_zero

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_step

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_even' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_even

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_odd' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_odd

example (Valid : P → Prop)
    (hzero : Valid zero)
    (hadd : ∀ left right, Valid left → Valid right → Valid (add left right))
    (hdouble : ∀ point, Valid point → Valid (double point))
    (scalar : Nat) (point : P) (hpoint : Valid point) :
    Valid (ScalarMul.binary zero add double scalar point) :=
  ScalarMul.binary_preserves zero add double Valid hzero hadd hdouble scalar point hpoint

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_preserves' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_preserves

example (point : G1Projective.Point) :
    ScalarMul.g1 0 point = G1Projective.infinity := ScalarMul.g1_zero point
example (point : G1Projective.Point) : ScalarMul.g1 1 point = point :=
  ScalarMul.g1_one point
example (point : G2Projective.Point) :
    ScalarMul.g2 0 point = G2Projective.infinity := ScalarMul.g2_zero point
example (point : G2Projective.Point) : ScalarMul.g2 1 point = point :=
  ScalarMul.g2_one point

#print axioms ScalarMul.g1_one
#print axioms ScalarMul.g2_one
#print axioms ScalarMul.loopG1_step

end Checks.Bls12381ScalarMul
