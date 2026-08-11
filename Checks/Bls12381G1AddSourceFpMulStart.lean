import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStart

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst final : EvmState)
    (Vend : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hbody : Interp.execStmt Challenge.EvmProof.modexpExec 67 fpMulFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody) =
        .ok (Vend, final, .normal)) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fpMulFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals
      [(VEnv.get Vend "\x0072").getD 0, (VEnv.get Vend "\x0073").getD 0]
      final) :=
  eval_fpMul_of_body ahi alo bhi blo yst final Vend hbody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpMul_of_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fpMul_of_body

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
