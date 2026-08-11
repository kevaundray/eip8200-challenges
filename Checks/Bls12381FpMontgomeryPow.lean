import Challenge.Bls12381.ProofSupport.FpMontgomeryPowBits

set_option warningAsError true

namespace Checks.Bls12381FpMontgomeryPow

open Challenge.Bls12381.ProofSupport

example : Fp.scanExponent [] = none := rfl

example : Fp.scanExponent [0, 0] = none := rfl

example : Fp.highestSetBit (UInt8.ofNat 1) = 0 := rfl
example : Fp.highestSetBit (UInt8.ofNat 2) = 1 := rfl
example : Fp.highestSetBit (UInt8.ofNat 128) = 7 := rfl

example : Fp.scanExponent [0, 5, 2] = some
    (UInt8.ofNat 5,
      [false, true, false, false, false, false, false, false, true, false]) :=
  rfl

example (byte : UInt8) : (Fp.byteBits byte).length = 8 :=
  Fp.length_byteBits byte

example (byte : UInt8) :
    Fp.binaryValue (Fp.significantByteBits byte) = byte.toNat :=
  Fp.binaryValue_significantByteBits byte

example (byte : UInt8) : Fp.binaryValue (Fp.byteBits byte) = byte.toNat :=
  Fp.binaryValue_byteBits byte

example (bytes : List UInt8) :
    Fp.bytesValue (Fp.dropLeadingZeroBytes bytes) = Fp.bytesValue bytes :=
  Fp.bytesValue_dropLeadingZeroBytes bytes

example (bytes : List UInt8) :
    Fp.binaryValue (Fp.exponentBits bytes) = Fp.bytesValue bytes :=
  Fp.binaryValue_exponentBits bytes

example {bytes : List UInt8} {first : UInt8} {remaining : List Bool}
    (hscan : Fp.scanExponent bytes = some (first, remaining)) :
    Fp.bytesValue bytes = 2 ^ remaining.length + Fp.binaryValue remaining :=
  Fp.scanExponent_value hscan

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.binaryValue_append

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_reverse_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_reverse_bits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_significantByteBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_significantByteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.bits_length_le_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.bits_length_le_eight

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.length_byteBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.length_byteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_replicate_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.binaryValue_replicate_false

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_byteBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_byteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.length_flatMap_byteBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.length_flatMap_byteBits

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_flatMap_byteBits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.binaryValue_flatMap_byteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.bytesValue_dropLeadingZeroBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.bytesValue_dropLeadingZeroBytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_exponentBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_exponentBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.reverse_bits_eq_true_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.reverse_bits_eq_true_cons

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.dropLeadingZeroBytes_head_ne_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.dropLeadingZeroBytes_head_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.scanExponent_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.scanExponent_value

end Checks.Bls12381FpMontgomeryPow
