import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulExec
set_option warningAsError true
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
#check step_fp2Mul
/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.step_fp2Mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fp2Mul
