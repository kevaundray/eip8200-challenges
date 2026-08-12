import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveStoresExec

set_option warningAsError true

/-! # Twist-constant addition in frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundArgs {V st args vals}
    (h : Interp.evalArgs Challenge.EvmProof.modexpExec 8 onCurveBodyFuns
      V st args = .ok (.vals vals st)) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      V st args (.vals vals st) :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 8).2.1
    _ _ _ _ _ h

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs
      V st stmt V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem lookup_fp2Add_onCurve : lookupFun onCurveBodyFuns "\x0014" =
    some (fp2AddDecl, fp2AddFuns) := by rfl

private theorem onCurveStmt7_shape : onCurveStmt7 =
    .exprStmt (.call "\x0014"
      [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)]) := by
  rfl

private theorem step_fp2AddBody (yst : EvmState) (out a b : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect fp2AddFuns
      (fp2AddInitialEnv out a b) yst (.block fp2AddBody)
      (fp2AddBodyResultEnv yst out a b) (fp2AddFinalState yst out a b)
      .normal :=
  soundStmt (exec_fp2AddBody yst out a b)

private theorem step_onCurveAdd (yst : EvmState) (x y : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
      (.call "\x0014"
        [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)])
      (.vals [] (onCurveStateAfterAdd yst x y)) := by
  have hargs := soundArgs (V := onCurveInitialEnv x y)
    (st := onCurveStateAfterConstant yst x y)
    (args := [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)])
    (vals := [BitVec.ofNat 256 2304, BitVec.ofNat 256 2304,
      BitVec.ofNat 256 2432]) (by rfl)
  have hcall := Step.callOk hargs lookup_fp2Add_onCurve (by rfl)
    (step_fp2AddBody (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2432)) (Or.inl rfl)
  simpa [fp2AddDecl, onCurveStateAfterAdd] using hcall

theorem exec_onCurveStmt7 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
      onCurveStmt7 (onCurveInitialEnv x y)
      (onCurveStateAfterAdd yst x y) .normal := by
  rw [onCurveStmt7_shape]
  exact Step.exprStmt (step_onCurveAdd yst x y)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
