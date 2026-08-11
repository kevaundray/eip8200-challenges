import Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

set_option warningAsError true

open YulSemantics YulSemantics.EVM

example {yst : EvmState}
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ Challenge.Bls12381G1Add.inputBytes)
    (hhalted : yst.halted = none) :
    ∃ yst',
      Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock
        yst [] yst' .halt ∧
      yst'.halted = some (.invalid, []) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_invalid_length
    hfit hsize hhalted

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_invalid_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_invalid_length
