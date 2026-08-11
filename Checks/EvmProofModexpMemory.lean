import Challenge.EvmProof.ModexpMemory

set_option warningAsError true

namespace Challenge.EvmProof.ModexpMemory

open EvmSemantics

example (memory : Nat → UInt8) (start size : Nat) :
    (readWindow memory start size).size = size :=
  readWindow_size memory start size

example (memory : Nat → UInt8) (start size offset width : Nat)
    (hfit : offset + width ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset width =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) width) :=
  bytesToNatPadded_readWindow memory start size offset width hfit

example (memory : Nat → UInt8) (start size offset : Nat)
    (hfit : offset + 32 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 32 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 32) :=
  bytesToNatPadded_readWindow32 memory start size offset hfit

example (memory : Nat → UInt8) (start size offset : Nat)
    (hfit : offset + 48 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 48 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 48) :=
  bytesToNatPadded_readWindow48 memory start size offset hfit

example (memory : Nat → UInt8) (start size offset : Nat)
    (hfit : offset + 96 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 96 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 96) :=
  bytesToNatPadded_readWindow96 memory start size offset hfit

/-- info: 'Challenge.EvmProof.ModexpMemory.readWindow_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms readWindow_size

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow32

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow48' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow48

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow96' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow96

end Challenge.EvmProof.ModexpMemory
