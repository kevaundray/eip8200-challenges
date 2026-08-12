import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFinitePostExec

set_option warningAsError true

/-! # G1ADD common post-slope checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainFinitePostBody =
    [mainFinitePostStmt0, mainFinitePostStmt1, mainFinitePostStmt2,
      mainFinitePostStmt3, mainFinitePostStmt4, mainFinitePostStmt5,
      mainFinitePostStmt6, mainFinitePostStmt7] :=
  mainFinitePostBody_eq

example : mainFinitePostStmt0 =
    Compilation.referenceCompiledBlock[28]! := rfl

example : mainFinitePostStmt7 =
    Compilation.referenceCompiledBlock[35]! := rfl

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFinitePostBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFinitePostBody

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
