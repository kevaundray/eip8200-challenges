import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDispatcherLawful

set_option warningAsError true

/-! # Complete G1ADD point-scope dispatcher -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- The point-scope suffix after the two infinity words and both curve
validation calls have completed. -/
def mainPointDispatcherBody : Block Op := mainPointScopeBody.drop 4

theorem mainPointDispatcherBody_eq : mainPointDispatcherBody =
    mainBothInfinityStmt :: mainFirstInfinityStmt ::
      [mainSecondInfinityStmt] := by
  rfl

private theorem mainBothInfinityStmt_shape_full : mainBothInfinityStmt =
    .cond (.builtin .and [.var "\x0096", .var "\x0097"])
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := by
  rfl

private theorem step_mainBothInfinity_skip (yst : EvmState)
    (hfirst : mainInf1 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainBothInfinityStmt
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainBothInfinityStmt_shape_full]
  have hfirstEval : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0096")
      (.vals [mainInf1 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hsecondEval : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0097")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .and [.var "\x0096", .var "\x0097"])
      (.vals [mainBothInfinityValue yst] (mainValidatedState yst)) := by
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hsecondEval) hfirstEval) rfl
  have hzero : mainBothInfinityValue yst =
      Challenge.EvmProof.modexpExec.toDialect.zero := by
    apply BitVec.eq_of_toNat_eq
    simp [mainBothInfinityValue, hfirst, Dialect.zero, EVM.litValue]
  exact Step.ifFalse hcondition hzero

private theorem mainFirstInfinityStmt_shape_full : mainFirstInfinityStmt =
    .cond (.var "\x0096")
      [.exprStmt
        (.call "\x0012"
          [.builtin .mload [.lit (.number 128)],
            .builtin .mload [.lit (.number 160)],
            .builtin .mload [.lit (.number 192)],
            .builtin .mload [.lit (.number 224)]]),
       .exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := by
  rfl

private theorem step_mainFirstInfinity_skip (yst : EvmState)
    (hfirst : mainInf1 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainFirstInfinityStmt
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainFirstInfinityStmt_shape_full]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0096")
      (.vals [mainInf1 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hzero : mainInf1 yst =
      Challenge.EvmProof.modexpExec.toDialect.zero := by
    rw [hfirst]
    rfl
  exact Step.ifFalse hcondition hzero

private theorem mainSecondInfinityStmt_shape_full : mainSecondInfinityStmt =
    .cond (.var "\x0097")
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := by
  rfl

private theorem step_mainSecondInfinity_skip (yst : EvmState)
    (hsecond : mainInf2 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainSecondInfinityStmt
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainSecondInfinityStmt_shape_full]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0097")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hzero : mainInf2 yst =
      Challenge.EvmProof.modexpExec.toDialect.zero := by
    rw [hsecond]
    rfl
  exact Step.ifFalse hcondition hzero

/-- Both finite infinity flags skip the complete lexical-scope suffix. -/
theorem step_mainPointDispatcher_finite (yst : EvmState)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      mainPointDispatcherBody (mainPointEnv yst)
      (mainValidatedState yst) .normal := by
  rw [mainPointDispatcherBody_eq]
  exact Step.seqCons (step_mainBothInfinity_skip yst hfirst)
    (Step.seqCons (step_mainFirstInfinity_skip yst hfirst)
      (Step.seqCons (step_mainSecondInfinity_skip yst hsecond) Step.seqNil))

/-- The top-level source suffix beginning with the two-word slope
declaration. -/
def mainFiniteTopBody : Block Op := Compilation.referenceCompiledBlock.drop 25

theorem mainFiniteTopBody_eq : mainFiniteTopBody =
    mainFiniteSlopeDecl :: mainFiniteDispatcherBody := by
  rfl

private theorem mainFiniteSlopeDecl_shape : mainFiniteSlopeDecl =
    .letDecl ["\x0098", "\x0099"] none := by
  rfl

private theorem step_mainFiniteSlopeDecl (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainValidatedState yst) mainFiniteSlopeDecl
      (mainFiniteEnv yst) (mainValidatedState yst) .normal := by
  rw [mainFiniteSlopeDecl_shape]
  simpa [mainFiniteEnv] using
    (Step.letZero
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := mainFuns) (V := [])
      (st := mainValidatedState yst)
      (vars := ["\x0098", "\x0099"]))

private theorem finitePrefix (yst : EvmState)
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect}
    {stend : EvmState} {outcome : Outcome}
    (htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst)
      mainFiniteDispatcherBody Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainValidatedState yst) mainFiniteTopBody Vend stend outcome := by
  rw [mainFiniteTopBody_eq]
  exact Step.seqCons (step_mainFiniteSlopeDecl yst) htail

/-- Complete point-scope dispatcher execution for nonexceptional doubling. -/
theorem step_mainPointDispatcher_double (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst = 0)
    (hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainValidatedState yst) mainFiniteTopBody
      (mainFinitePostEnv5 yst (mainFiniteDoubleResultEnv yst)
        (mainFiniteDoublePostState yst) (mainFiniteDoubleLambdaWords yst))
      (mainFinitePostReturnState yst (mainFiniteDoublePostState yst)
        (mainFiniteDoubleLambdaWords yst)) .halt :=
  finitePrefix yst
    (step_mainFiniteDispatcher_double yst hxeq hyeq hyzero hx hy)

/-- Complete point-scope dispatcher execution for unequal x-coordinates. -/
theorem step_mainPointDispatcher_unequal (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 0)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainValidatedState yst) mainFiniteTopBody
      (mainFinitePostEnv5 yst (mainFiniteUnequalResultEnv yst)
        (mainFiniteUnequalFinalState yst) (mainFiniteUnequalLambdaWords yst))
      (mainFinitePostReturnState yst (mainFiniteUnequalFinalState yst)
        (mainFiniteUnequalLambdaWords yst)) .halt :=
  finitePrefix yst
    (step_mainFiniteDispatcher_unequal yst hxeq hx1 hx2)

/-- Complete point-scope dispatcher execution for opposite finite points. -/
theorem step_mainPointDispatcher_opposite (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainValidatedState yst) mainFiniteTopBody (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt :=
  finitePrefix yst
    (step_mainFiniteDispatcher_opposite yst hxeq hyeq)

/-- Complete point-scope dispatcher execution for doubling at `y = 0`. -/
theorem step_mainPointDispatcher_zeroY (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainValidatedState yst) mainFiniteTopBody (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt :=
  finitePrefix yst
    (step_mainFiniteDispatcher_zeroY yst hxeq hyeq hyzero)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
