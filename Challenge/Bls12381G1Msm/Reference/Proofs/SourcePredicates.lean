import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePredicateDefs
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGeValue

set_option warningAsError true

/-! Executable and lawful-limb semantics of the frozen field predicates. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

def fpValidValue (hi lo : U256) : U256 :=
  b2w (fpGeModulusValue hi lo = 0)

def fpZeroValue (hi lo : U256) : U256 :=
  b2w (hi = 0) &&& b2w (lo = 0)

def fpEqValue (ahi alo bhi blo : U256) : U256 :=
  b2w (ahi = bhi) &&& b2w (alo = blo)

theorem conv_fpValidValue (hi lo : U256) :
    YulEvmCompiler.conv (fpValidValue hi lo) =
    UInt256.isZero
      (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }) := by
  unfold fpValidValue
  rw [YulEvmCompiler.conv_iszero, conv_fpGeModulusValue]

theorem conv_fpZeroValue (hi lo : U256) :
    YulEvmCompiler.conv (fpZeroValue hi lo) =
    UInt256.land (UInt256.isZero (YulEvmCompiler.conv hi))
      (UInt256.isZero (YulEvmCompiler.conv lo)) := by
  unfold fpZeroValue
  rw [YulEvmCompiler.conv_and, YulEvmCompiler.conv_iszero,
    YulEvmCompiler.conv_iszero]

theorem conv_fpEqValue (ahi alo bhi blo : U256) :
    YulEvmCompiler.conv (fpEqValue ahi alo bhi blo) =
    UInt256.land (UInt256.eq (YulEvmCompiler.conv ahi) (YulEvmCompiler.conv bhi))
      (UInt256.eq (YulEvmCompiler.conv alo) (YulEvmCompiler.conv blo)) := by
  unfold fpEqValue
  rw [YulEvmCompiler.conv_and, YulEvmCompiler.conv_eq,
    YulEvmCompiler.conv_eq]

theorem eval_fpZero (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 sourceFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x002" [.var "hi", .var "lo"]) =
    .ok (.vals [fpZeroValue hi lo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookup_fpZero, fpZeroDecl, fpZeroBody_eq, fpZeroStmt,
    modexpExec, modexpBuiltinFn, stepOp, bin, un, fpZeroValue,
    Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set, bindZeros, restore]

theorem eval_fpEq (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x003" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [fpEqValue ahi alo bhi blo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookup_fpEq, fpEqDecl, fpEqBody_eq, fpEqStmt,
    modexpExec, modexpBuiltinFn, stepOp, bin, fpEqValue,
    Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set, bindZeros, restore]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
