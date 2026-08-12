import Challenge.Bls12381G2Msm.Reference.Proofs.SourceMsmPointHelpers
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Relational call transport for the G2MSM point helpers. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem exec_msmCopyPointBody (dst src : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fp2Funs
      [("\x00141", dst), ("\x00142", src)] yst
      (.block msmCopyPointBody) =
    .ok ([("\x00141", dst), ("\x00142", src)],
      msmCopyPointState yst dst src, .normal) := by
  let V := [("\x00141", dst), ("\x00142", src)]
  have hpre : Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst msmCopyPointPrefix =
      .ok (V, msmCopyPointMidState yst dst src, .normal) := by rfl
  have htail : Interp.execStmts Challenge.EvmProof.modexpExec 62
      ([] :: fp2Funs) V (msmCopyPointMidState yst dst src)
      msmCopyPointTail =
      .ok (V, msmCopyPointState yst dst src, .normal) := by rfl
  have hbody := Interp.execStmts_append_normal
    (E := Challenge.EvmProof.modexpExec) (n := 62)
    (pre := msmCopyPointPrefix) (tail := msmCopyPointTail)
    (by omega) hpre htail
  have hlen : msmCopyPointPrefix.length = 4 := by rfl
  rw [hlen] at hbody
  rw [Interp.execStmt, msmCopyPointBody_eq]
  rw [show hoist Challenge.EvmProof.modexpExec.toDialect
    (msmCopyPointPrefix ++ msmCopyPointTail) = [] by rfl]
  change (do
    let result ← Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst (msmCopyPointPrefix ++ msmCopyPointTail)
    .ok (restore V result.1, result.2.1, result.2.2)) = _
  rw [hbody]
  rfl

theorem step_msmCopyPoint_of_args {funs V st argState args}
    (dst src : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [dst, src] argState))
    (hlookup : lookupFun funs "\x0027" =
      some (msmCopyPointDecl, fp2Funs)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0027" args) (.vals [] (msmCopyPointState argState dst src)) := by
  have hbody := soundStmt (exec_msmCopyPointBody dst src argState)
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [msmCopyPointDecl] using hcall

def pointInfinityInitialEnv (ptr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00143", ptr), ("\x00144", 0)]

def pointInfinityFinalEnv (yst : EvmState) (ptr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointInfinityInitialEnv ptr) "\x00144" (pointZeroValue yst ptr)

private theorem exec_pointInfinityBody (ptr : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fp2Funs
      (pointInfinityInitialEnv ptr) yst (.block pointInfinityBody) =
    .ok (pointInfinityFinalEnv yst ptr,
      pointZeroReadState yst ptr, .normal) := by rfl

theorem step_pointInfinity_of_args {funs V st argState args} (ptr : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [ptr] argState))
    (hlookup : lookupFun funs "\x0028" =
      some (pointInfinityDecl, fp2Funs)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0028" args)
      (.vals [pointZeroValue argState ptr]
        (pointZeroReadState argState ptr)) := by
  have hbody := soundStmt (exec_pointInfinityBody ptr argState)
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [pointInfinityDecl, pointInfinityInitialEnv,
    pointInfinityFinalEnv, VEnv.get, VEnv.set] using hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
