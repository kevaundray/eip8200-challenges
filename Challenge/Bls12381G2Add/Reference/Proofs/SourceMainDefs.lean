import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointStoresExec

set_option warningAsError true

/-! # Frozen G2ADD main decode and validation definitions -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def mainLengthStmt : Stmt Op := Compilation.referenceCompiledBlock[25]!

def mainStore0 : Stmt Op := Compilation.referenceCompiledBlock[26]!
def mainStore1 : Stmt Op := Compilation.referenceCompiledBlock[27]!
def mainStore2 : Stmt Op := Compilation.referenceCompiledBlock[28]!
def mainStore3 : Stmt Op := Compilation.referenceCompiledBlock[29]!
def mainStore4 : Stmt Op := Compilation.referenceCompiledBlock[30]!
def mainStore5 : Stmt Op := Compilation.referenceCompiledBlock[31]!
def mainStore6 : Stmt Op := Compilation.referenceCompiledBlock[32]!
def mainStore7 : Stmt Op := Compilation.referenceCompiledBlock[33]!
def mainStore8 : Stmt Op := Compilation.referenceCompiledBlock[34]!
def mainStore9 : Stmt Op := Compilation.referenceCompiledBlock[35]!
def mainStore10 : Stmt Op := Compilation.referenceCompiledBlock[36]!
def mainStore11 : Stmt Op := Compilation.referenceCompiledBlock[37]!
def mainStore12 : Stmt Op := Compilation.referenceCompiledBlock[38]!
def mainStore13 : Stmt Op := Compilation.referenceCompiledBlock[39]!
def mainStore14 : Stmt Op := Compilation.referenceCompiledBlock[40]!
def mainStore15 : Stmt Op := Compilation.referenceCompiledBlock[41]!

def mainStores : List (Stmt Op) :=
  [mainStore0, mainStore1, mainStore2, mainStore3,
    mainStore4, mainStore5, mainStore6, mainStore7,
    mainStore8, mainStore9, mainStore10, mainStore11,
    mainStore12, mainStore13, mainStore14, mainStore15]

def mainValidationStmt : Stmt Op := Compilation.referenceCompiledBlock[42]!
def mainPointScope : Stmt Op := Compilation.referenceCompiledBlock[43]!

def mainPointScopeBody : Block Op :=
  match mainPointScope with
  | .block body => body
  | _ => []

def mainInputWord (yst : EvmState) (offset : Nat) : U256 :=
  wordFrom yst.env.calldata offset

private def mainStoreWord (yst : EvmState) (offset : Nat) : EvmState :=
  { touchMemory yst offset 32 with
    memory := storeWord yst.memory offset (mainInputWord yst offset) }

def mainDecodedState (yst : EvmState) : EvmState :=
  let s0 := mainStoreWord yst 0
  let s1 := mainStoreWord s0 32
  let s2 := mainStoreWord s1 64
  let s3 := mainStoreWord s2 96
  let s4 := mainStoreWord s3 128
  let s5 := mainStoreWord s4 160
  let s6 := mainStoreWord s5 192
  let s7 := mainStoreWord s6 224
  let s8 := mainStoreWord s7 256
  let s9 := mainStoreWord s8 288
  let s10 := mainStoreWord s9 320
  let s11 := mainStoreWord s10 352
  let s12 := mainStoreWord s11 384
  let s13 := mainStoreWord s12 416
  let s14 := mainStoreWord s13 448
  mainStoreWord s14 480

def mainDecodedWord (yst : EvmState) (offset : Nat) : U256 :=
  loadWord (mainDecodedState yst).memory offset

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
