import Challenge.Bls12381.ProofSupport.MapToG1Map

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG1

example (u : Field) : G1Affine.OnCurve (mapBeforeCofactor u) :=
  mapBeforeCofactor_onCurve u

example (u : Field) : G1Affine.OnCurve (map u) := map_onCurve u

example (u : Field) : Codec.ValidG1 (G1Affine.toWire (map u)) :=
  map_toWire_valid u

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.mapBeforeCofactor_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapBeforeCofactor_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.map_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.map_toWire_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_toWire_valid

end Challenge.Bls12381.ProofSupport.MapToG1
