import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulInput

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` call and output state -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpMulFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

def fpMulBody : Block Op :=
  match Compilation.referenceCompiledBlock[9]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpMulDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0068", "\x0069", "\x0070", "\x0071"]
    rets := ["\x0072", "\x0073"]
    body := fpMulBody }

theorem lookup_fpMul : lookupFun fpMulFuns "\x009" =
    some (fpMulDecl, fpMulFuns) := by
  rfl

def fpMulInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0068", ahi), ("\x0069", alo), ("\x0070", bhi), ("\x0071", blo),
    ("\x0072", 0), ("\x0073", 0)]

def fpMulReducedValue (ahi alo bhi blo : U256) : Nat :=
  ((convFullMul (fullMulValue ahi alo bhi blo)).value %
    EvmSemantics.Crypto.Bls12381.p)

def fpMulOutputBytes (ahi alo bhi blo : U256) : ByteArray :=
  Precompile.natToBytes (fpMulReducedValue ahi alo bhi blo) 48

def fpMulResponse (yst : EvmState) (ahi alo bhi blo : U256) : CallResponse :=
  { success := true
    returndata := (fpMulOutputBytes ahi alo bhi blo).toList
    world := CallWorld.ofState (fpMulInputState yst ahi alo bhi blo) }

def fpMulCallState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  finishCall .staticcall (fpMulInputState yst ahi alo bhi blo)
    (fpMulResponse yst ahi alo bhi blo) 1024 241 1280 48

def fpMulResult (yst : EvmState) (ahi alo bhi blo : U256) : U256 × U256 :=
  (loadWord (fpMulCallState yst ahi alo bhi blo).memory 1280 >>> 128,
    loadWord (fpMulCallState yst ahi alo bhi blo).memory 1296)

def fpMulFinalState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  touchMemory (touchMemory (fpMulCallState yst ahi alo bhi blo) 1280 32)
    1296 32

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
