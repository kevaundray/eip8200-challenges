import Challenge.Bls12381.ProofSupport.MapToG2Map

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG2

example (u : Field) : mapBeforeCofactor u =
    let mapped := sourceSswu u
    iso3 mapped.xN mapped.xD mapped.y := mapBeforeCofactor_eq u

example (u : Field) :
    map u = ScalarMul.g2 hEff (mapBeforeCofactor u) := map_eq u

example (u : Field) : G2Affine.OnCurve (mapBeforeCofactor u) :=
  mapBeforeCofactor_onCurve u

example (u : Field) : G2Affine.OnCurve (map u) := map_onCurve u

example (u : Field) : Codec.ValidG2 (G2Affine.toWire (map u)) :=
  map_toWire_valid u

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.mapBeforeCofactor_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapBeforeCofactor_eq

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_eq

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.mapBeforeCofactor_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapBeforeCofactor_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.map_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.map_toWire_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_toWire_valid

end Challenge.Bls12381.ProofSupport.MapToG2
