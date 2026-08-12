import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddRefinement

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check fp2AddResult_eq_addSource
#check fp2AddResult_canonical
#check fp2AddResult_toField

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddResult_eq_addSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2AddResult_eq_addSource
