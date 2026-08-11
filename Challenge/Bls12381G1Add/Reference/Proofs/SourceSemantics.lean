import Challenge.Bls12381G1Add.Reference.Proofs.Compilation
import Challenge.Bls12381.ProofSupport.FpAddSub
import Challenge.EvmProof.ModexpExec

set_option warningAsError true

/-!
# Source semantics of the proof-friendly G1ADD runtime

The proofs in this directory connect the frozen normalized source block to
the local EIP-correct G1 specification.  They use the deterministic MODEXP
sub-interpreter only to construct derivations of the same open relational
dialect consumed by compiler correctness.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof
open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

/-- Source-word form of the high-first BLS modulus comparison. -/
def fpGeModulusValue (hi lo : U256) : U256 :=
  b2w (BitVec.ult
      (BitVec.ofNat 256 34565483545414906068789196026815425751) hi) |||
    (b2w (hi = BitVec.ofNat 256
      34565483545414906068789196026815425751) &&&
      b2w (b2w (BitVec.ult lo
        (BitVec.ofNat 256
          45442060874369865957053122457065728162598490762543039060009208264153100167851)) = 0))

/-- Source-word validity predicate, defined by the frozen source's negation of
the modulus comparison helper. -/
def fpValidValue (hi lo : U256) : U256 :=
  b2w (fpGeModulusValue hi lo = 0)

theorem conv_fpGeModulusValue (hi lo : U256) :
    YulEvmCompiler.conv (fpGeModulusValue hi lo) =
    Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo } := by
  have hhi : YulEvmCompiler.conv (BitVec.ofNat 256
      34565483545414906068789196026815425751) =
      Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  have hlo : YulEvmCompiler.conv (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167851) =
      Challenge.Bls12381.ProofSupport.Fp.modulusLo := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  unfold fpGeModulusValue
  rw [YulEvmCompiler.conv_or, YulEvmCompiler.conv_gt,
    YulEvmCompiler.conv_and, YulEvmCompiler.conv_eq,
    YulEvmCompiler.conv_iszero, YulEvmCompiler.conv_lt, hhi, hlo]
  rfl

theorem conv_fpValidValue (hi lo : U256) :
    YulEvmCompiler.conv (fpValidValue hi lo) =
    UInt256.isZero
      (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }) := by
  unfold fpValidValue
  rw [YulEvmCompiler.conv_iszero, conv_fpGeModulusValue]

private def isFunctionDefinition {Op : Type} : Stmt Op → Bool
  | .funDef .. => true
  | _ => false

private theorem execStmts_function_prefix
    (E : ExecDialect) [DecidableEq E.toDialect.Value]
    (defs rest : List (Stmt E.toDialect.Op))
    (hdefs : defs.all isFunctionDefinition = true)
    (fuel : Nat) (hfuel : 0 < fuel) (funs V st) :
    Interp.execStmts E (fuel + defs.length) funs V st (defs ++ rest) =
      Interp.execStmts E fuel funs V st rest := by
  induction defs with
  | nil => simp
  | cons head tail ih =>
      have hparts : isFunctionDefinition head = true ∧
          tail.all isFunctionDefinition = true := by
        simpa using hdefs
      cases head <;> simp only [isFunctionDefinition, Bool.false_eq_true] at hparts
      all_goals try { exact False.elim hparts.1 }
      case funDef name params rets body =>
        have hpositive : 0 < fuel + tail.length := by omega
        obtain ⟨k, hk⟩ : ∃ k, fuel + tail.length = k + 1 :=
          ⟨fuel + tail.length - 1, by omega⟩
        rw [show fuel + (Stmt.funDef name params rets body :: tail).length =
          (k + 1) + 1 by simp; omega]
        change Interp.execStmts E (k + 1) funs V st
          (tail ++ rest) = Interp.execStmts E fuel funs V st rest
        rw [← hk]
        exact ih hparts.2

private def invalidLengthStmt : Stmt Op :=
  .cond
    (.builtin .iszero
      [.builtin .eq [.builtin .calldatasize [], .lit (.number 256)]])
    [.exprStmt (.builtin .invalid [])]

private theorem reference_after_functions :
    referenceCompiledBlock.drop 13 =
      invalidLengthStmt :: referenceCompiledBlock.drop 14 := by
  rfl

private theorem reference_function_prefix :
    (referenceCompiledBlock.take 13).all isFunctionDefinition = true := by
  rfl

private theorem reference_function_prefix_length :
    (referenceCompiledBlock.take 13).length = 13 := by
  rfl

private theorem exec_reference_function_prefix (funs V st) :
    Interp.execStmts modexpExec 127 funs V st referenceCompiledBlock =
      Interp.execStmts modexpExec 114 funs V st
        (invalidLengthStmt :: referenceCompiledBlock.drop 14) := by
  have hprefix := execStmts_function_prefix modexpExec
    (referenceCompiledBlock.take 13) (referenceCompiledBlock.drop 13)
    reference_function_prefix 114 (by omega) funs V st
  rw [reference_function_prefix_length] at hprefix
  norm_num at hprefix
  calc
    Interp.execStmts modexpExec 127 funs V st referenceCompiledBlock =
        Interp.execStmts modexpExec 127 funs V st
          (referenceCompiledBlock.take 13 ++ referenceCompiledBlock.drop 13) := by
      rw [List.take_append_drop]
    _ = Interp.execStmts modexpExec 114 funs V st
          (referenceCompiledBlock.drop 13) := hprefix
    _ = Interp.execStmts modexpExec 114 funs V st
          (invalidLengthStmt :: referenceCompiledBlock.drop 14) := by
      rw [reference_after_functions]

/-- The first frozen helper implements the high-first modulus comparison used
by the approved source-faithful Fp schedules. -/
theorem eval_fpGeModulus (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x000" [.var "hi", .var "lo"]) =
    .ok (.vals [fpGeModulusValue hi lo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookupFun, hoist, referenceCompiledBlock, frozenReferenceBlock,
    modexpExec, modexpBuiltinFn, stepOp, bin, un, fpGeModulusValue,
    Dialect.zero, restore]
  rfl

/-- The second frozen helper negates `fpGeModulus` exactly once. -/
theorem eval_fpValid (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [fpValidValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

private theorem calldataSizeWord_ne {yst : EvmState}
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ Challenge.Bls12381G1Add.inputBytes) :
    BitVec.ofNat 256 yst.env.calldata.length ≠ BitVec.ofNat 256 256 := by
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hfit] at hnat
  apply hsize
  simpa [Challenge.Bls12381G1Add.inputBytes,
    Challenge.Bls12381.ProofSupport.Codec.g1Bytes] using hnat

private theorem exec_invalidLengthStmt {yst : EvmState} (funs V)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ Challenge.Bls12381G1Add.inputBytes) :
    Interp.execStmt modexpExec 113 funs V yst invalidLengthStmt =
      .ok (V, { yst with halted := some (.invalid, []) }, .halt) := by
  have hword := calldataSizeWord_ne hfit hsize
  simp [invalidLengthStmt, Interp.execStmt, Interp.execStmts,
    Interp.evalExpr, Interp.evalArgs, modexpExec, modexpBuiltinFn, stepOp,
    bin, un, rd0, litValue, b2w, Dialect.zero, restore, hword]

/-- A wrong calldata length takes the first source-level `invalid()` branch. -/
theorem run_invalid_length {yst : EvmState}
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ Challenge.Bls12381G1Add.inputBytes)
    (_hhalted : yst.halted = none) :
    ∃ yst',
      Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
        referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.invalid, []) := by
  let yst' : EvmState := { yst with halted := some (.invalid, []) }
  refine ⟨yst', modexpExec_run_sound (fuel := 128) ?_, rfl⟩
  unfold Interp.run
  simp only [Interp.execStmt]
  rw [exec_reference_function_prefix]
  rw [Interp.execStmts]
  rw [exec_invalidLengthStmt _ _ hfit hsize]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
