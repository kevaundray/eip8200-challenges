import Challenge.Bls12381.ProofSupport.LawfulAffine

set_option warningAsError true

namespace Checks.Bls12381LawfulAffine

open Challenge.Bls12381.ProofSupport.LawfulAffine

variable {F : Type} [Field F] [DecidableEq F]

example (curve : Curve F) (point : Point F) :
    add curve .infinity point = point := infinity_add curve point

example (curve : Curve F) (point : Point F) :
    add curve point .infinity = point := add_infinity curve point

example (curve : Curve F) (x y : F) :
    add curve (.affine x y) (.affine x (-y)) = .infinity :=
  add_opposite curve x y

example (curve : Curve F) (x : F) :
    double curve (.affine x 0) = .infinity := double_y_zero curve x

example (curve : Curve F) (point : Point F) (h2 : (2 : F) ≠ 0) :
    OnCurve curve point -> OnCurve curve (double curve point) :=
  onCurve_double curve point h2

example (curve : Curve F) (left right : Point F) (h2 : (2 : F) ≠ 0) :
    OnCurve curve left -> OnCurve curve right ->
      OnCurve curve (add curve left right) :=
  onCurve_add curve left right h2

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.onCurve_neg' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms onCurve_neg

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.onCurve_double' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms onCurve_double

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.onCurve_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms onCurve_add

end Checks.Bls12381LawfulAffine
