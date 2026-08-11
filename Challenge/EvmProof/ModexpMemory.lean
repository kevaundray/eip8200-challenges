import Challenge.EvmProof.Bytes

set_option warningAsError true

/-! # Functional-memory windows for MODEXP -/

namespace Challenge.EvmProof.ModexpMemory

open EvmSemantics

/-- Package a finite window of the Yul interpreter's functional memory as the
byte-array input consumed by native precompiles. -/
def readWindow (memory : Nat → UInt8) (start size : Nat) : ByteArray :=
  ⟨(YulSemantics.EVM.readBytes memory start size).toArray⟩

@[simp] theorem readWindow_size (memory : Nat → UInt8) (start size : Nat) :
    (readWindow memory start size).size = size := by
  change (YulSemantics.EVM.readBytes memory start size).length = size
  simp [YulSemantics.EVM.readBytes]

/-- Parsing a fitting subwindow of functional memory is the same big-endian
byte fold as reading that subwindow directly. -/
theorem bytesToNatPadded_readWindow (memory : Nat → UInt8)
    (start size offset width : Nat) (hfit : offset + width ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset width =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) width) := by
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList]
  rw [Challenge.EvmProof.Bytes.readPadded_toList]
  apply congrArg Challenge.EvmProof.Bytes.bytesNat
  unfold YulSemantics.EVM.readBytes
  apply List.map_congr_left
  intro i hi
  have hiWidth : i < width := by simpa using hi
  unfold YulSemantics.EVM.byteFrom readWindow
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  simp only [List.getD_eq_getElem?_getD]
  unfold YulSemantics.EVM.readBytes
  rw [List.getElem?_map]
  rw [List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  congr 1
  omega

theorem bytesToNatPadded_readWindow32 (memory : Nat → UInt8)
    (start size offset : Nat) (hfit : offset + 32 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 32 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 32) :=
  bytesToNatPadded_readWindow memory start size offset 32 hfit

theorem bytesToNatPadded_readWindow48 (memory : Nat → UInt8)
    (start size offset : Nat) (hfit : offset + 48 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 48 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 48) :=
  bytesToNatPadded_readWindow memory start size offset 48 hfit

theorem bytesToNatPadded_readWindow96 (memory : Nat → UInt8)
    (start size offset : Nat) (hfit : offset + 96 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 96 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 96) :=
  bytesToNatPadded_readWindow memory start size offset 96 hfit

end Challenge.EvmProof.ModexpMemory
