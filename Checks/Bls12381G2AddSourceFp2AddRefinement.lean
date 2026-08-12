import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check fp2AddResult_eq_addSource
#check fp2AddResult_canonical
#check fp2AddResult_toField
#check Fp2AddRunContract
#check fp2Add_contract_exists
#check fp2AddContractState
#check eval_fp2AddContractState
#check fp2AddContractState_output
#check fp2AddContractState_loadWord_before_out
#check fp2AddContractState_fp2At_before_out
#check fp2AddScheduledB_eq_after_out_c0
#check fp2AddContractState_output_inplace_right_after

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddResult_eq_addSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2AddResult_eq_addSource

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2Add_contract_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2Add_contract_exists
