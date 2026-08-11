import Challenge.Bls12381G1Add.Reference.Proofs.SourceMul

set_option warningAsError true

/-! # Frozen G1ADD field-memory helpers -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- High source word of the BLS12-381 base-field modulus. -/
def fpModulusHiValue : U256 := BitVec.ofNat 256
  34565483545414906068789196026815425751

/-- Low source word of the BLS12-381 base-field modulus. -/
def fpModulusLoValue : U256 := BitVec.ofNat 256
  45442060874369865957053122457065728162598490762543039060009208264153100167851

/-- State after the exact two-`MSTORE` source schedule that writes a 48-byte
field element starting at `ptr`. -/
def storeFpState (yst : EvmState) (ptr hi lo : U256) : EvmState :=
  let first :=
    { touchMemory yst ptr.toNat 32 with
      memory := storeWord yst.memory ptr.toNat (hi <<< 128) }
  let nextPtr := ptr + BitVec.ofNat 256 16
  { touchMemory first nextPtr.toNat 32 with
    memory := storeWord first.memory nextPtr.toNat lo }

/-- The eighth frozen helper executes the two source-ordered field stores. -/
theorem eval_storeFp (ptr hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("ptr", ptr), ("hi", hi), ("lo", lo)] yst
      (.call "\x007" [.var "ptr", .var "hi", .var "lo"]) =
    .ok (.vals [] (storeFpState yst ptr hi lo)) := by
  rw [Interp.evalExpr]
  rfl

/-- The ninth frozen helper stores the exact BLS12-381 modulus words. -/
theorem eval_storeModulus (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("ptr", ptr)] yst (.call "\x008" [.var "ptr"]) =
    .ok (.vals [] (storeFpState yst ptr fpModulusHiValue fpModulusLoValue)) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
