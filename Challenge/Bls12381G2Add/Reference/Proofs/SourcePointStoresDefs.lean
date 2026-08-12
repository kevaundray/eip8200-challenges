import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointPredicatesRefinement

set_option warningAsError true

/-! # Frozen G2ADD point output helper definitions -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def storeConstState (yst : EvmState) (dest : Nat) (value : U256) :
    EvmState :=
  { touchMemory yst dest 32 with memory := storeWord yst.memory dest value }

private def copyWordState (yst : EvmState) (dest : Nat) (src : U256) :
    EvmState :=
  let read := touchMemory yst src.toNat 32
  { touchMemory read dest 32 with
    memory := storeWord read.memory dest (loadWord yst.memory src.toNat) }

private theorem copyWordState_memory (yst : EvmState) (dest : Nat)
    (src : U256) :
    (copyWordState yst dest src).memory =
      storeWord yst.memory dest (loadWord yst.memory src.toNat) := rfl

def clearPointState (yst : EvmState) : EvmState :=
  let s0 := storeConstState yst 0 0
  let s1 := storeConstState s0 32 0
  let s2 := storeConstState s1 64 0
  let s3 := storeConstState s2 96 0
  let s4 := storeConstState s3 128 0
  let s5 := storeConstState s4 160 0
  let s6 := storeConstState s5 192 0
  storeConstState s6 224 0

def copyPointState (yst : EvmState) (point : U256) : EvmState :=
  let s0 := copyWordState yst 0 point
  let s1 := copyWordState s0 32 (point + BitVec.ofNat 256 32)
  let s2 := copyWordState s1 64 (point + BitVec.ofNat 256 64)
  let s3 := copyWordState s2 96 (point + BitVec.ofNat 256 96)
  let s4 := copyWordState s3 128 (point + BitVec.ofNat 256 128)
  let s5 := copyWordState s4 160 (point + BitVec.ofNat 256 160)
  let s6 := copyWordState s5 192 (point + BitVec.ofNat 256 192)
  copyWordState s6 224 (point + BitVec.ofNat 256 224)

def storePointState (yst : EvmState) (x y : U256) : EvmState :=
  let s0 := copyWordState yst 0 x
  let s1 := copyWordState s0 32 (x + BitVec.ofNat 256 32)
  let s2 := copyWordState s1 64 (x + BitVec.ofNat 256 64)
  let s3 := copyWordState s2 96 (x + BitVec.ofNat 256 96)
  let s4 := copyWordState s3 128 y
  let s5 := copyWordState s4 160 (y + BitVec.ofNat 256 32)
  let s6 := copyWordState s5 192 (y + BitVec.ofNat 256 64)
  copyWordState s6 224 (y + BitVec.ofNat 256 96)

/-- At the fixed postlude scratch addresses, the eight point copies read the
original high-memory words.  This shallow memory boundary keeps output-codec
proofs from unfolding the nested source helper. -/
theorem storePointState_memory_2688_2944 (yst : EvmState) :
    (storePointState yst 2688 2944).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 0 (loadWord yst.memory 2688))
                    32 (loadWord yst.memory 2720))
                  64 (loadWord yst.memory 2752))
                96 (loadWord yst.memory 2784))
              128 (loadWord yst.memory 2944))
            160 (loadWord yst.memory 2976))
        192 (loadWord yst.memory 3008))
        224 (loadWord yst.memory 3040) := by
  have hx0 : ((2688 : U256).toNat) = 2688 := by decide
  have hx1 : (2688 + BitVec.ofNat 256 32 : U256).toNat = 2720 := by decide
  have hx2 : (2688 + BitVec.ofNat 256 64 : U256).toNat = 2752 := by decide
  have hx3 : (2688 + BitVec.ofNat 256 96 : U256).toNat = 2784 := by decide
  have hy0 : ((2944 : U256).toNat) = 2944 := by decide
  have hy1 : (2944 + BitVec.ofNat 256 32 : U256).toNat = 2976 := by decide
  have hy2 : (2944 + BitVec.ofNat 256 64 : U256).toNat = 3008 := by decide
  have hy3 : (2944 + BitVec.ofNat 256 96 : U256).toNat = 3040 := by decide
  simp only [storePointState, copyWordState_memory]
  rw [hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by omega)]

def clearPointBody : Block Op :=
  match Compilation.referenceCompiledBlock[22]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def clearPointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := [], rets := [], body := clearPointBody }

theorem lookup_clearPoint : lookupFun fp2Funs "\x0022" =
    some (clearPointDecl, fp2Funs) := by rfl

def copyPointBody : Block Op :=
  match Compilation.referenceCompiledBlock[23]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def copyPointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00128"], rets := [], body := copyPointBody }

theorem lookup_copyPoint : lookupFun fp2Funs "\x0023" =
    some (copyPointDecl, fp2Funs) := by rfl

def storePointBody : Block Op :=
  match Compilation.referenceCompiledBlock[24]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def storePointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00129", "\x00130"], rets := [], body := storePointBody }

theorem lookup_storePoint : lookupFun fp2Funs "\x0024" =
    some (storePointDecl, fp2Funs) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
