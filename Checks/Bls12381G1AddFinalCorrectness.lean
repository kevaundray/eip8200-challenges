import Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness

set_option warningAsError true

open Challenge.Bls12381G1Add
open Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness

#check gasSchedule
#check reference_correctWithSchedule
#check reference_correct

example : CorrectWithSchedule referenceBytecode gasSchedule :=
  reference_correctWithSchedule

example : Correct referenceBytecode := reference_correct

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness.reference_correctWithSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reference_correctWithSchedule

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reference_correct
