import Challenge.Bls12381G1Add.Reference.Proofs.SourceStore

set_option warningAsError true

open YulSemantics YulSemantics.EVM

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

example (ptr hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("ptr", ptr), ("hi", hi), ("lo", lo)] yst
      (.call "\x007" [.var "ptr", .var "hi", .var "lo"]) =
    .ok (.vals [] (storeFpState yst ptr hi lo)) :=
  eval_storeFp ptr hi lo yst

example (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("ptr", ptr)] yst (.call "\x008" [.var "ptr"]) =
    .ok (.vals [] (storeFpState yst ptr fpModulusHiValue fpModulusLoValue)) :=
  eval_storeModulus ptr yst

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_storeFp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_storeFp

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_storeModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_storeModulus

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
