import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDispatcher

set_option warningAsError true

/-! # Complete G1ADD finite-dispatch checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainFiniteDispatcherBody =
    mainFiniteEqualStmt :: mainFiniteUnequalStmt :: mainFinitePostBody :=
  mainFiniteDispatcherBody_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteDoubleFinalState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteDoubleFinalState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteUnequalFinalState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteUnequalFinalState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteDispatcher_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteDispatcher_opposite

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteDispatcher_zeroY' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteDispatcher_zeroY

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteDispatcher_double' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteDispatcher_double

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteDispatcher_unequal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteDispatcher_unequal

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
