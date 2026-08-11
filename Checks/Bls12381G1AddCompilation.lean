import Challenge.Bls12381G1Add.Reference.Proofs.Compilation

set_option warningAsError true

open Challenge.Bls12381G1Add
open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

#guard toString (repr referenceParsedCompiledBlock) ==
  toString (repr referenceCompiledBlock)

example : (YulEvmCompiler.compileProgram referenceCompiledBlock).isSome :=
  referenceCompileProgramSucceeded

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompileProgramSucceeded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCompileProgramSucceeded

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiled_compileProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCompiled_compileProgram
