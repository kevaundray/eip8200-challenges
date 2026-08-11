import Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness

example : EvmSemantics.EVM.Precompile.isPrecompileWithConfig
    Challenge.Bls12381G1Add.executionConfig .Osaka
      EvmSemantics.EVM.Precompile.modexpAddress = true :=
  executionConfig_modexp_enabled

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness.executionConfig_modexp_enabled' does not depend on any axioms -/
#guard_msgs in
#print axioms executionConfig_modexp_enabled

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness.referenceCompiledBlock_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCompiledBlock_correct
