import Challenge.EvmProof.Limbs

set_option warningAsError true

namespace Checks.EvmProofWideMul

open EvmSemantics
open Challenge.EvmProof

example (a b : UInt256) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 :=
  Word.word_toNat_mul a b

example (base x y z : Nat) :
    Nat.ofDigits base [x, y, z] = x + base * y + base ^ 2 * z :=
  Limbs.ofDigits_three base x y z

example (x y z : UInt256) :
    x.toNat + Limbs.radix * y.toNat + Limbs.radix ^ 2 * z.toNat <
      Limbs.radix ^ 3 :=
  Limbs.threeWords_lt x y z

example (base value : Nat) (hbase : 0 < base) :
    Limbs.joinAt base (Limbs.splitAt base value) = value :=
  Limbs.join_splitAt hbase value

example (base a b : Nat) (hbase : 0 < base) :
    Limbs.joinAt base (Limbs.mulSplit base a b) = a * b :=
  Limbs.join_mulSplit hbase a b

example (base x y z : Nat) (hbase : 0 < base)
    (hx : x < base) (hy : y < base) (hz : z < base) :
    Limbs.joinAt base (Limbs.addThreeAt base x y z) = x + y + z :=
  Limbs.join_addThreeAt hbase hx hy hz

example (a b : UInt256) :
    Limbs.WideProduct.value (Limbs.fullMul256 a b) = a.toNat * b.toNat :=
  Limbs.fullMul256_value a b

example (a b : Limbs.WideProduct) :
    (Limbs.subWide256 a b).value =
      if b.value ≤ a.value then a.value - b.value
      else Limbs.radix ^ 2 + a.value - b.value :=
  Limbs.subWide256_value a b

example (a b : Limbs.WideProduct) :
    (Limbs.subWide256 a b).value =
      (a.value + Limbs.radix ^ 2 - b.value) % Limbs.radix ^ 2 :=
  Limbs.subWide256_value_mod a b

example (a b : Limbs.WideProduct) :
    (Limbs.wideGeWord a b).toNat ≠ 0 ↔ b.value ≤ a.value :=
  Limbs.wideGeWord_nonzero_iff a b

example (a b : Limbs.WideProduct) :
    (Limbs.conditionalSubWide256 a b).value =
      if b.value ≤ a.value then a.value - b.value else a.value :=
  Limbs.conditionalSubWide256_value a b

example (a b : Limbs.WideProduct) :
    (Limbs.mulWideLow256 a b).value =
      (a.value * b.value) % Limbs.radix ^ 2 :=
  Limbs.mulWideLow256_value a b

example (x y z : UInt256) :
    (Limbs.addThree256 x y z).value = x.toNat + y.toNat + z.toNat :=
  Limbs.addThree256_value x y z

example (x y z : UInt256) :
    (Limbs.addThree256 x y z).carry.toNat < 3 :=
  Limbs.addThree256_carry_lt_three x y z

example (sum : Limbs.WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < Limbs.radix) :
    (sum.add term).value = sum.value + term.toNat :=
  Limbs.WordSum.value_add sum term hcarry

example (sum : Limbs.WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < Limbs.radix) :
    (sum.add term).carry.toNat ≤ sum.carry.toNat + 1 :=
  Limbs.WordSum.carry_add_le sum term hcarry

example (a b : UInt256) :
    (Limbs.fullMul256 a b).lo.toNat < Limbs.radix ∧
      (Limbs.fullMul256 a b).hi.toNat < Limbs.radix :=
  Limbs.fullMul256_words_lt a b

/-- info: 'Challenge.EvmProof.Limbs.join_mulSplit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.join_mulSplit

/-- info: 'Challenge.EvmProof.Limbs.mulSplit_high_eq_mersenne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.mulSplit_high_eq_mersenne

/-- info: 'Challenge.EvmProof.Limbs.fullMul256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.fullMul256_value

/-- info: 'Challenge.EvmProof.Limbs.join_addThreeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.join_addThreeAt

/-- info: 'Challenge.EvmProof.Limbs.addThree256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.addThree256_value

/-- info: 'Challenge.EvmProof.Limbs.addThree256_carry_lt_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.addThree256_carry_lt_three

/-- info: 'Challenge.EvmProof.Limbs.WordSum.value_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.WordSum.value_add

/-- info: 'Challenge.EvmProof.Limbs.WordSum.carry_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.WordSum.carry_add_le

/-- info: 'Challenge.EvmProof.Limbs.ofDigits_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.ofDigits_three

/-- info: 'Challenge.EvmProof.Limbs.threeWords_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.threeWords_lt

/-- info: 'Challenge.EvmProof.Limbs.subWide256_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.subWide256_value

/-- info: 'Challenge.EvmProof.Limbs.subWide256_value_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.subWide256_value_mod

/-- info: 'Challenge.EvmProof.Word.word_toNat_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Word.word_toNat_mul

/-- info: 'Challenge.EvmProof.Limbs.mulWideLow256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.mulWideLow256_value

/-- info: 'Challenge.EvmProof.Word.word_toNat_gt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Word.word_toNat_gt

/-- info: 'Challenge.EvmProof.Word.word_toNat_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Word.word_toNat_eq

/-- info: 'Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.wideGeWord_nonzero_iff

/-- info: 'Challenge.EvmProof.Limbs.conditionalSubWide256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.conditionalSubWide256_value

end Checks.EvmProofWideMul
