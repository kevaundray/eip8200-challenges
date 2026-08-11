import Challenge.Bls12381.ProofSupport.FpMontgomeryPow

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

/-! The loop squares before its conditional multiply and consumes bits in
source order after the initial most-significant one. -/

example (baseM acc : Fp.Limbs) :
    Fp.montgomeryBitStep baseM acc false = Fp.montMul2 acc acc :=
  rfl

example (baseM acc : Fp.Limbs) :
    Fp.montgomeryBitStep baseM acc true =
      Fp.montMul2 (Fp.montMul2 acc acc) baseM :=
  rfl

example (base : Fp.Limbs) : Fp.montgomeryPow base [] = Fp.montgomeryOne :=
  rfl

example (base : Fp.Limbs) : Fp.montgomeryPow base [0, 0] = Fp.montgomeryOne :=
  rfl

example (base : Fp.Limbs) :
    Fp.montgomeryPow base [1] = Fp.montgomeryEncode base :=
  rfl

example {baseM acc : Fp.Limbs} (hbaseM : Fp.Canonical baseM)
    (hacc : Fp.Canonical acc) (bit : Bool) :
    Fp.Canonical (Fp.montgomeryBitStep baseM acc bit) :=
  Fp.canonical_montgomeryBitStep hbaseM hacc bit

example {baseM acc : Fp.Limbs} (hbaseM : Fp.Canonical baseM)
    (hacc : Fp.Canonical acc) (bits : List Bool) :
    Fp.Canonical (Fp.foldMontgomeryBits baseM acc bits) :=
  Fp.canonical_foldMontgomeryBits hbaseM hacc bits

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : List UInt8) :
    Fp.Canonical (Fp.montgomeryPow base exponent) :=
  Fp.canonical_montgomeryPow hbase exponent

example (base : Fp.Limbs) :
    Fp.montgomeryPow base [2] =
      Fp.montMul2 (Fp.montgomeryEncode base) (Fp.montgomeryEncode base) :=
  rfl

example (base : Fp.Limbs) :
    Fp.montgomeryPow base [3] =
      Fp.montMul2
        (Fp.montMul2 (Fp.montgomeryEncode base) (Fp.montgomeryEncode base))
        (Fp.montgomeryEncode base) :=
  rfl

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

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryBitStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryBitStep

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_foldMontgomeryBits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_foldMontgomeryBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_montgomeryPow

end Checks.Bls12381FpMontgomeryPow
