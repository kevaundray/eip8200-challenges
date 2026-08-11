import Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

set_option warningAsError true

open YulSemantics YulSemantics.EVM

example (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x000" [.var "hi", .var "lo"]) =
    .ok (.vals [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
      hi lo] yst) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpGeModulus
    hi lo yst

example (hi lo : U256) :
    YulEvmCompiler.conv
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue hi lo) =
    Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo } :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpGeModulusValue
    hi lo

example (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpValidValue
      hi lo] yst) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpValid hi lo yst

example (hi lo : U256) :
    YulEvmCompiler.conv
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpValidValue hi lo) =
    EvmSemantics.UInt256.isZero
      (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpValidValue hi lo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpValid

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpValidValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpValidValue

example (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x002" [.var "hi", .var "lo"]) =
    .ok (.vals [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue
      hi lo] yst) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpZero hi lo yst

example (hi lo : U256) :
    YulEvmCompiler.conv
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue hi lo) =
    EvmSemantics.UInt256.land
      (EvmSemantics.UInt256.isZero (YulEvmCompiler.conv hi))
      (EvmSemantics.UInt256.isZero (YulEvmCompiler.conv lo)) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpZeroValue hi lo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpZero

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpZeroValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpZeroValue

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpGeModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpGeModulus

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpGeModulusValue' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpGeModulusValue

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
