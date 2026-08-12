import Challenge.Bls12381G1Add.Reference.Proofs.SourceRun

set_option warningAsError true

/-! # Complete G1ADD frozen-source run checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_double' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_double

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_unequal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_unequal

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_opposite

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_zeroY' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_zeroY

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
