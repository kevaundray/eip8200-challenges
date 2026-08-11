import Challenge.EvmProof.Limbs

set_option warningAsError true

namespace Checks.EvmProofWideMul

open EvmSemantics
open Challenge.EvmProof

example (base value : Nat) (hbase : 0 < base) :
    Limbs.joinAt base (Limbs.splitAt base value) = value :=
  Limbs.join_splitAt hbase value

example (base a b : Nat) (hbase : 0 < base) :
    Limbs.joinAt base (Limbs.mulSplit base a b) = a * b :=
  Limbs.join_mulSplit hbase a b

example (a b : UInt256) :
    Limbs.WideProduct.value (Limbs.fullMul256 a b) = a.toNat * b.toNat :=
  Limbs.fullMul256_value a b

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

end Checks.EvmProofWideMul
