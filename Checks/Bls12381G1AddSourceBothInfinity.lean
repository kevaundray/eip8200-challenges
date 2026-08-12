import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainBothInfinity

set_option warningAsError true

/-! # Frozen G1ADD both-infinity return checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainBothInfinityStmt = mainPointScopeBody[4]! := rfl

example : mainBothInfinityStmt =
    .cond (.builtin .and [.var "\x0096", .var "\x0097"])
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := rfl

example (yst : EvmState) (hboth : mainBothInfinityValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainBothInfinityStmt
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt :=
  step_mainBothInfinity_return yst hboth

example (yst : EvmState)
    (hcalldata : yst.env.calldata = List.replicate 256 0) :
    (mainBothInfinityReturnState yst).halted =
      some (HaltKind.ret, List.replicate 128 0) :=
  mainBothInfinity_returned_zero_bytes yst hcalldata

example (yst : EvmState)
    (hcalldata : yst.env.calldata = List.replicate 256 0) :
    (mainBothInfinityReturnState yst).halted =
      some (HaltKind.ret,
        Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (.infinity : EvmSemantics.Crypto.Bls12381.Point) |>.toList) :=
  mainBothInfinity_returned_infinity yst hcalldata

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainBothInfinity_return' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainBothInfinity_return

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainBothInfinity_returned_zero_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainBothInfinity_returned_zero_bytes

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainBothInfinity_returned_infinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainBothInfinity_returned_infinity

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
