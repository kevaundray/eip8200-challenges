import Challenge.Bls12381.ProofSupport.MsmSubgroup

set_option warningAsError true

namespace Checks.Bls12381MsmSubgroup

open Challenge.Bls12381.ProofSupport

example (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1Affine (MsmSemantics.g1Value terms) = true :=
  MsmSubgroup.g1_output terms hterms

example (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2Affine (MsmSemantics.g2Value terms) = true :=
  MsmSubgroup.g2_output terms hterms

example (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1 (G1Affine.toWire (MsmSemantics.g1Value terms)) = true :=
  MsmSubgroup.g1_wire_output terms hterms

example (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2 (G2Affine.toWire (MsmSemantics.g2Value terms)) = true :=
  MsmSubgroup.g2_wire_output terms hterms

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g1MathSum_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSubgroup.g1MathSum_nsmul_zero

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g2MathSum_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSubgroup.g2MathSum_nsmul_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g1_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g1_output

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g2_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g2_output

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g1_wire_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g1_wire_output

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g2_wire_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g2_wire_output

end Checks.Bls12381MsmSubgroup
