import Challenge.Bls12381.ProofSupport.AffineGroup

set_option warningAsError true

namespace Checks.Bls12381AffineGroup

open Challenge.Bls12381.ProofSupport

variable {F : Type} [Field F] [DecidableEq F]
variable (curve : LawfulAffine.Curve F)
variable [WeierstrassCurve.IsElliptic (AffineGroup.mathCurve curve)]
variable (h2 : (2 : F) ≠ 0)

example : AffineGroup.toMathlib curve (AffineGroup.infinity curve) = 0 :=
  AffineGroup.toMathlib_infinity curve

example (left right : AffineGroup.Point curve) :
    AffineGroup.toMathlib curve (AffineGroup.add curve h2 left right) =
      AffineGroup.toMathlib curve left + AffineGroup.toMathlib curve right :=
  AffineGroup.toMathlib_add curve h2 left right

example (point : AffineGroup.Point curve) :
    AffineGroup.toMathlib curve (AffineGroup.double curve h2 point) =
      AffineGroup.toMathlib curve point + AffineGroup.toMathlib curve point :=
  AffineGroup.toMathlib_double curve h2 point

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroup.equation_of_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroup.equation_of_onCurve

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroup.toMathlib_infinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroup.toMathlib_infinity

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroup.toMathlib_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroup.toMathlib_add

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroup.toMathlib_double' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroup.toMathlib_double

end Checks.Bls12381AffineGroup
