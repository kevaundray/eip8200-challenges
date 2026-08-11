import Challenge.Bls12381.ProofSupport.MapToG1Isogeny

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG1

example : kXNum.length = 12 := kXNum_length
example : kXDen.length = 11 := kXDen_length
example : kYNum.length = 16 := kYNum_length
example : kYDen.length = 16 := kYDen_length

example : kXNumSourceOrder = kXNum.reverse := rfl
example : kXDenSourceOrder = kXDen.reverse.tail := rfl
example : kYNumSourceOrder = kYNum.reverse := rfl
example : kYDenSourceOrder = kYDen.reverse.tail := rfl

example (c0 c1 numerator denominator : Field) :
    evalHom [c0, c1] numerator denominator =
      c0 * denominator + numerator * c1 := by
  simp [evalHom]

example (numerator denominator y : Field)
    (hpole :
      let values := iso11Components numerator denominator
      values.xDen * denominator = 0 ∨ values.yDen = 0) :
    iso11 numerator denominator y = G1Affine.infinity :=
  iso11_eq_infinity_of_pole numerator denominator y hpole

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.kXNum_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kXNum_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.kXDen_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kXDen_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.kYNum_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kYNum_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.kYDen_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kYDen_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.iso11_eq_infinity_of_pole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iso11_eq_infinity_of_pole

end Challenge.Bls12381.ProofSupport.MapToG1
