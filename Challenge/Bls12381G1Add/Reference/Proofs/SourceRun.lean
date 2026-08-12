import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFull

set_option warningAsError true

/-! # Complete frozen G1ADD source runs -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- The executable top-level body after its thirteen function definitions. -/
def mainValidBody : Block Op := Compilation.referenceCompiledBlock.drop 13

theorem mainValidBody_eq : mainValidBody =
    mainDecodePrefix ++ mainPointScope :: mainFiniteTopBody := by
  rfl

private theorem step_append_normal
    {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hprefix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vmid stmid .normal)
    (hsuffix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil =>
      cases hprefix
      simpa using hsuffix
  | cons head rest ih =>
      cases hprefix with
      | seqCons hhead htail =>
        simpa using Step.seqCons hhead (ih htail hsuffix)
      | seqStop _ hnot => exact (hnot rfl).elim

private theorem step_append_halt
    {funs V st pre Vend stend suffix}
    (hprefix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vend stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend .halt := by
  induction pre generalizing V st Vend stend with
  | nil => cases hprefix
  | cons head rest ih =>
      cases hprefix with
      | seqCons hhead htail =>
        simpa using Step.seqCons hhead (ih htail)
      | seqStop hhead hnot => exact Step.seqStop hhead hnot

private theorem step_mainValid_double (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst = 0)
    (hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody
      (mainFinitePostEnv5 yst (mainFiniteDoubleResultEnv yst)
        (mainFiniteDoublePostState yst) (mainFiniteDoubleLambdaWords yst))
      (mainFinitePostReturnState yst (mainFiniteDoublePostState yst)
        (mainFiniteDoubleLambdaWords yst)) .halt := by
  rw [mainValidBody_eq]
  have hdecode := step_mainDecodePrefix_success yst hsize hpadding hcanonical
  have hscope := step_mainPointScope_finite yst hcurve1 hcurve2 hfirst hsecond
  have htail := step_mainPointDispatcher_double yst hxeq hyeq hyzero hx hy
  exact step_append_normal hdecode (Step.seqCons hscope htail)

private theorem step_mainValid_of_finiteTail (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect}
    {stend : EvmState}
    (htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainValidatedState yst) mainFiniteTopBody Vend stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody Vend stend .halt := by
  rw [mainValidBody_eq]
  exact step_append_normal
    (step_mainDecodePrefix_success yst hsize hpadding hcanonical)
    (Step.seqCons
      (step_mainPointScope_finite yst hcurve1 hcurve2 hfirst hsecond) htail)

private theorem step_mainValid_unequal (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 0)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody
      (mainFinitePostEnv5 yst (mainFiniteUnequalResultEnv yst)
        (mainFiniteUnequalFinalState yst) (mainFiniteUnequalLambdaWords yst))
      (mainFinitePostReturnState yst (mainFiniteUnequalFinalState yst)
        (mainFiniteUnequalLambdaWords yst)) .halt :=
  step_mainValid_of_finiteTail yst hsize hpadding hcanonical hcurve1 hcurve2
    hfirst hsecond (step_mainPointDispatcher_unequal yst hxeq hx1 hx2)

private theorem step_mainValid_opposite (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt :=
  step_mainValid_of_finiteTail yst hsize hpadding hcanonical hcurve1 hcurve2
    hfirst hsecond (step_mainPointDispatcher_opposite yst hxeq hyeq)

private theorem step_mainValid_zeroY (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt :=
  step_mainValid_of_finiteTail yst hsize hpadding hcanonical hcurve1 hcurve2
    hfirst hsecond
      (step_mainPointDispatcher_zeroY yst hxeq hyeq hyzero)

private theorem step_mainValid_of_pointHalt (yst stend : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hscope : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterCanonicalReads yst) mainPointScope [] stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] stend .halt := by
  rw [mainValidBody_eq]
  exact step_append_normal
    (step_mainDecodePrefix_success yst hsize hpadding hcanonical)
    (Step.seqStop hscope (by decide))

private theorem step_mainValid_bothInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainBothInfinityReturnState yst) .halt :=
  step_mainValid_of_pointHalt yst _ hsize hpadding hcanonical
    (step_mainPointScope_bothInfinity yst hcurve1 hcurve2 hboth)

private theorem step_mainValid_firstInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainFirstInfinityReturnState yst) .halt :=
  step_mainValid_of_pointHalt yst _ hsize hpadding hcanonical
    (step_mainPointScope_firstInfinity yst hcurve1 hcurve2 hfirst hsecond)

private theorem step_mainValid_secondInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainSecondInfinityReturnState yst) .halt :=
  step_mainValid_of_pointHalt yst _ hsize hpadding hcanonical
    (step_mainPointScope_secondInfinity yst hcurve1 hcurve2 hfirst hsecond)

private theorem step_mainValid_padding_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainInvalidState (mainAfterPaddingReads yst)) .halt := by
  rw [mainValidBody_eq]
  exact step_append_halt
    (step_mainDecodePrefix_padding_reject yst hsize hpadding)

private theorem step_mainValid_canonical_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody []
      (mainInvalidState (mainAfterCanonicalReads yst)) .halt := by
  rw [mainValidBody_eq]
  exact step_append_halt
    (step_mainDecodePrefix_canonical_reject yst hsize hpadding hcanonical)

private theorem step_mainValid_curve1_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainInvalidState (mainAfterCurve1 yst)) .halt := by
  rw [mainValidBody_eq]
  exact step_append_normal
    (step_mainDecodePrefix_success yst hsize hpadding hcanonical)
    (Step.seqStop (step_mainPointScope_curve1_reject yst hcurve1) (by decide))

private theorem step_mainValid_curve2_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainInvalidState (mainValidatedState yst)) .halt := by
  rw [mainValidBody_eq]
  exact step_append_normal
    (step_mainDecodePrefix_success yst hsize hpadding hcanonical)
    (Step.seqStop
      (step_mainPointScope_curve2_reject yst hcurve1 hcurve2) (by decide))

private def isFunctionDefinition : Stmt Op → Bool
  | .funDef .. => true
  | _ => false

private theorem step_function_definitions
    (defs : Block Op) (hdefs : defs.all isFunctionDefinition = true)
    (funs : FunEnv Challenge.EvmProof.modexpExec.toDialect)
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V yst defs
      V yst .normal := by
  induction defs with
  | nil => exact Step.seqNil
  | cons head tail ih =>
      have hparts : isFunctionDefinition head = true ∧
          tail.all isFunctionDefinition = true := by
        simpa using hdefs
      cases head <;>
        simp only [isFunctionDefinition, Bool.false_eq_true] at hparts
      all_goals try { exact False.elim hparts.1 }
      case funDef => exact Step.seqCons Step.funDef (ih hparts.2)

private theorem reference_function_prefix :
    (Compilation.referenceCompiledBlock.take 13).all
      isFunctionDefinition = true := by
  rfl

private theorem reference_decompose : Compilation.referenceCompiledBlock =
    Compilation.referenceCompiledBlock.take 13 ++ mainValidBody := by
  exact (List.take_append_drop 13 Compilation.referenceCompiledBlock).symm

private theorem run_of_mainValid (yst stend : EvmState)
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect}
    (hmain : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody Vend stend .halt) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst [] stend .halt := by
  have hdefs := step_function_definitions
    (Compilation.referenceCompiledBlock.take 13) reference_function_prefix
    mainFuns [] yst
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      Compilation.referenceCompiledBlock Vend stend .halt := by
    rw [reference_decompose]
    exact step_append_normal hdefs hmain
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hbody
  simpa [Run, mainFuns, restore] using hblock

/-- A relational summary of the complete both-infinity source path.

The returned state is intentionally abstract: consumers see the execution,
selected return value, and the frame facts of the final `return(0, 128)` stage,
but not the expanded `mainBothInfinityReturnState`. The comparison state for
the frame is the state immediately before that return.

Gas is not part of `YulSemantics.EVM.EvmState`; it remains a separate
compiled-EVM contract rather than being approximated at this source layer. -/
structure MainBothInfinityContract (yst final : EvmState) : Prop where
  run : Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
    Compilation.referenceCompiledBlock yst [] final .halt
  returned : final.halted = some (.ret,
    readBytes (mainValidatedState yst).memory 0 128)
  memory_eq : final.memory = (mainValidatedState yst).memory
  activeWords_eq : final.activeWords = BitVec.ofNat 256
    (activeWordsAfter (mainValidatedState yst).activeWords.toNat 0 128)
  storage_eq : final.storage = (mainValidatedState yst).storage
  transient_eq : final.transient = (mainValidatedState yst).transient
  env_eq : final.env = (mainValidatedState yst).env
  returndata_eq : final.returndata = (mainValidatedState yst).returndata
  logs_eq : final.logs = (mainValidatedState yst).logs
  selfdestructs_eq : final.selfdestructs =
    (mainValidatedState yst).selfdestructs

/-- The exact frozen source runs through the complete nonexceptional doubling
path and halts with the already-refined canonical output state. -/
theorem run_main_double (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst = 0)
    (hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFinitePostReturnState yst (mainFiniteDoublePostState yst)
        (mainFiniteDoubleLambdaWords yst)) .halt := by
  have hmain := step_mainValid_double yst hsize hpadding hcanonical
    hcurve1 hcurve2 hfirst hsecond hxeq hyeq hyzero hx hy
  exact run_of_mainValid yst _ hmain

/-- The exact frozen source runs through the unequal-x affine branch. -/
theorem run_main_unequal (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 0)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst)) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFinitePostReturnState yst (mainFiniteUnequalFinalState yst)
        (mainFiniteUnequalLambdaWords yst)) .halt :=
  run_of_mainValid yst _ (step_mainValid_unequal yst hsize hpadding
    hcanonical hcurve1 hcurve2 hfirst hsecond hxeq hx1 hx2)

/-- The exact frozen source returns infinity for opposite finite points. -/
theorem run_main_opposite (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst = 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFiniteOppositeReturnState yst) .halt :=
  run_of_mainValid yst _ (step_mainValid_opposite yst hsize hpadding
    hcanonical hcurve1 hcurve2 hfirst hsecond hxeq hyeq)

/-- The exact frozen source returns infinity for doubling at `y = 0`. -/
theorem run_main_zeroY (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFiniteZeroYReturnState yst) .halt :=
  run_of_mainValid yst _ (step_mainValid_zeroY yst hsize hpadding
    hcanonical hcurve1 hcurve2 hfirst hsecond hxeq hyeq hyzero)

theorem run_main_bothInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainBothInfinityReturnState yst) .halt :=
  run_of_mainValid yst _ (step_mainValid_bothInfinity yst hsize hpadding
    hcanonical hcurve1 hcurve2 hboth)

/-- The complete both-infinity path, exposed through a relational boundary
instead of an equality to a fully expanded final state. -/
theorem run_main_bothInfinity_contract (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ∃ final, MainBothInfinityContract yst final := by
  refine ⟨mainBothInfinityReturnState yst, ?_⟩
  refine {
    run := run_main_bothInfinity yst hsize hpadding hcanonical hcurve1 hcurve2 hboth
    returned := ?_
    memory_eq := ?_
    activeWords_eq := ?_
    storage_eq := ?_
    transient_eq := ?_
    env_eq := ?_
    returndata_eq := ?_
    logs_eq := ?_
    selfdestructs_eq := ?_ }
  all_goals simp only [mainBothInfinityReturnState, touchMemory]

/-- The selected return-value view needed by the source specification. -/
theorem MainBothInfinityContract.returned_inputWindow
    {yst final : EvmState} (contract : MainBothInfinityContract yst final)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList) :
    final.halted = some (HaltKind.ret,
      (EvmSemantics.MachineState.readPadded input 0 128).toList) := by
  calc
    final.halted = (mainBothInfinityReturnState yst).halted := by
      rw [contract.returned]
      rfl
    _ = _ := mainBothInfinity_returned_inputWindow yst input hcalldata

theorem run_main_firstInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFirstInfinityReturnState yst) .halt :=
  run_of_mainValid yst _ (step_mainValid_firstInfinity yst hsize hpadding
    hcanonical hcurve1 hcurve2 hfirst hsecond)

theorem run_main_secondInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst ≠ 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainSecondInfinityReturnState yst) .halt :=
  run_of_mainValid yst _ (step_mainValid_secondInfinity yst hsize hpadding
    hcanonical hcurve1 hcurve2 hfirst hsecond)

theorem run_main_padding_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst ≠ 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState (mainAfterPaddingReads yst)) .halt :=
  run_of_mainValid yst _ (step_mainValid_padding_reject yst hsize hpadding)

theorem run_main_canonical_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst = 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState (mainAfterCanonicalReads yst)) .halt :=
  run_of_mainValid yst _
    (step_mainValid_canonical_reject yst hsize hpadding hcanonical)

theorem run_main_curve1_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst ≠ 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState (mainAfterCurve1 yst)) .halt :=
  run_of_mainValid yst _
    (step_mainValid_curve1_reject yst hsize hpadding hcanonical hcurve1)

theorem run_main_curve2_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst ≠ 0) :
    Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState (mainValidatedState yst)) .halt :=
  run_of_mainValid yst _ (step_mainValid_curve2_reject yst hsize hpadding
    hcanonical hcurve1 hcurve2)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
