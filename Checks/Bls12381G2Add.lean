import Challenge.Bls12381G2Add
set_option warningAsError true

/--
info: 'Challenge.Bls12381G2Add.correct_of_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.correct_of_schedule

/-- info: 'Challenge.Bls12381G2Add.deployAddress_not_precompile' does not depend on any axioms -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.deployAddress_not_precompile
