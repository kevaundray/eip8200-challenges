import Challenge.Bls12381.ProofSupport.Fp

set_option warningAsError true

/-!
# BLS12-381 fixed Barrett quotient schedule

This module models the six full-word products and carry chains used by
`Fp.sol` to obtain quotient limbs three and four.  It is separate from the
final division/correction proof so Lean can compile and reuse the large
reconstruction theorem without re-elaborating its proof term.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

structure BarrettPartials where
  p00 : Challenge.EvmProof.Limbs.WideProduct
  p01 : Challenge.EvmProof.Limbs.WideProduct
  p02 : Challenge.EvmProof.Limbs.WideProduct
  p10 : Challenge.EvmProof.Limbs.WideProduct
  p11 : Challenge.EvmProof.Limbs.WideProduct
  p12 : Challenge.EvmProof.Limbs.WideProduct
deriving DecidableEq, Repr

def barrettPartials (product : SchoolbookProduct) : BarrettPartials :=
  { p00 := Challenge.EvmProof.Limbs.fullMul256 product.r1 barrettMu0
    p01 := Challenge.EvmProof.Limbs.fullMul256 product.r1 barrettMu1
    p02 := Challenge.EvmProof.Limbs.fullMul256 product.r1 barrettMu2
    p10 := Challenge.EvmProof.Limbs.fullMul256 product.r2 barrettMu0
    p11 := Challenge.EvmProof.Limbs.fullMul256 product.r2 barrettMu1
    p12 := Challenge.EvmProof.Limbs.fullMul256 product.r2 barrettMu2 }

def barrettL1 (partials : BarrettPartials) : Challenge.EvmProof.Limbs.WordSum :=
  Challenge.EvmProof.Limbs.addThree256
    partials.p00.hi partials.p01.lo partials.p10.lo

def barrettL2 (partials : BarrettPartials) : Challenge.EvmProof.Limbs.WordSum :=
  ((Challenge.EvmProof.Limbs.addThree256
    partials.p01.hi partials.p10.hi partials.p02.lo).add
      partials.p11.lo).add (barrettL1 partials).carry

def barrettL3 (partials : BarrettPartials) : Challenge.EvmProof.Limbs.WordSum :=
  (Challenge.EvmProof.Limbs.addThree256
    partials.p02.hi partials.p11.hi partials.p12.lo).add
      (barrettL2 partials).carry

structure BarrettQuotient where
  q1 : UInt256
  q0 : UInt256
deriving DecidableEq, Repr

namespace BarrettQuotient

def value (quotient : BarrettQuotient) : Nat :=
  quotient.q0.toNat + Challenge.EvmProof.Limbs.radix * quotient.q1.toNat

end BarrettQuotient

/-- Exact quotient-limb schedule from `Fp.sol`: these are product limbs three
and four of `(r2:r1) * (M2:M1:M0)`. -/
def barrettQuotient (product : SchoolbookProduct) : BarrettQuotient :=
  let partials := barrettPartials product
  let l3 := barrettL3 partials
  { q0 := l3.word, q1 := partials.p12.hi + l3.carry }

def barrettQuotientTop (product : SchoolbookProduct) : Nat :=
  let partials := barrettPartials product
  partials.p12.hi.toNat + (barrettL3 partials).carry.toNat

theorem barrettSchedule_value (product : SchoolbookProduct) :
    let partials := barrettPartials product
    let l1 := barrettL1 partials
    let l2 := barrettL2 partials
    let l3 := barrettL3 partials
    (product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
        barrettMu =
      partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix * l1.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 3 * l3.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 4 *
        (partials.p12.hi.toNat + l3.carry.toNat) := by
  dsimp only
  let partials := barrettPartials product
  let l1 := barrettL1 partials
  let l2base := Challenge.EvmProof.Limbs.addThree256
    partials.p01.hi partials.p10.hi partials.p02.lo
  let l2a := l2base.add partials.p11.lo
  let l2 := l2a.add l1.carry
  let l3base := Challenge.EvmProof.Limbs.addThree256
    partials.p02.hi partials.p11.hi partials.p12.lo
  let l3 := l3base.add l2.carry
  have hR : 5 < Challenge.EvmProof.Limbs.radix := by
    norm_num [Challenge.EvmProof.Limbs.radix]
  have hl1 := Challenge.EvmProof.Limbs.addThree256_value
    partials.p00.hi partials.p01.lo partials.p10.lo
  have hl1carry := Challenge.EvmProof.Limbs.addThree256_carry_lt_three
    partials.p00.hi partials.p01.lo partials.p10.lo
  change l1.value = partials.p00.hi.toNat + partials.p01.lo.toNat +
    partials.p10.lo.toNat at hl1
  change l1.carry.toNat < 3 at hl1carry
  have hl2base := Challenge.EvmProof.Limbs.addThree256_value
    partials.p01.hi partials.p10.hi partials.p02.lo
  have hl2baseCarry := Challenge.EvmProof.Limbs.addThree256_carry_lt_three
    partials.p01.hi partials.p10.hi partials.p02.lo
  change l2base.value = partials.p01.hi.toNat + partials.p10.hi.toNat +
    partials.p02.lo.toNat at hl2base
  change l2base.carry.toNat < 3 at hl2baseCarry
  have hl2a := Challenge.EvmProof.Limbs.WordSum.value_add
    l2base partials.p11.lo (by omega)
  have hl2aCarryLe := Challenge.EvmProof.Limbs.WordSum.carry_add_le
    l2base partials.p11.lo (by omega)
  change l2a.value = l2base.value + partials.p11.lo.toNat at hl2a
  change l2a.carry.toNat ≤ l2base.carry.toNat + 1 at hl2aCarryLe
  have hl2aCarry : l2a.carry.toNat < 4 :=
    hl2aCarryLe.trans_lt (by omega)
  have hl2 := Challenge.EvmProof.Limbs.WordSum.value_add
    l2a l1.carry (by omega)
  have hl2CarryLe := Challenge.EvmProof.Limbs.WordSum.carry_add_le
    l2a l1.carry (by omega)
  change l2.value = l2a.value + l1.carry.toNat at hl2
  change l2.carry.toNat ≤ l2a.carry.toNat + 1 at hl2CarryLe
  have hl2Carry : l2.carry.toNat < 5 :=
    hl2CarryLe.trans_lt (by omega)
  have hl3base := Challenge.EvmProof.Limbs.addThree256_value
    partials.p02.hi partials.p11.hi partials.p12.lo
  have hl3baseCarry := Challenge.EvmProof.Limbs.addThree256_carry_lt_three
    partials.p02.hi partials.p11.hi partials.p12.lo
  change l3base.value = partials.p02.hi.toNat + partials.p11.hi.toNat +
    partials.p12.lo.toNat at hl3base
  change l3base.carry.toNat < 3 at hl3baseCarry
  have hl3 := Challenge.EvmProof.Limbs.WordSum.value_add
    l3base l2.carry (by omega)
  change l3.value = l3base.value + l2.carry.toNat at hl3
  have hl2value : l2.value = partials.p01.hi.toNat + partials.p10.hi.toNat +
      partials.p02.lo.toNat + partials.p11.lo.toNat + l1.carry.toNat := by
    calc
      l2.value = l2a.value + l1.carry.toNat := hl2
      _ = l2base.value + partials.p11.lo.toNat + l1.carry.toNat := by rw [hl2a]
      _ = partials.p01.hi.toNat + partials.p10.hi.toNat +
          partials.p02.lo.toNat + partials.p11.lo.toNat +
          l1.carry.toNat := by rw [hl2base]
  have hl3value : l3.value = partials.p02.hi.toNat + partials.p11.hi.toNat +
      partials.p12.lo.toNat + l2.carry.toNat := by
    calc
      l3.value = l3base.value + l2.carry.toNat := hl3
      _ = partials.p02.hi.toNat + partials.p11.hi.toNat +
          partials.p12.lo.toNat + l2.carry.toNat := by rw [hl3base]
  have hp00 := Challenge.EvmProof.Limbs.fullMul256_value product.r1 barrettMu0
  have hp01 := Challenge.EvmProof.Limbs.fullMul256_value product.r1 barrettMu1
  have hp02 := Challenge.EvmProof.Limbs.fullMul256_value product.r1 barrettMu2
  have hp10 := Challenge.EvmProof.Limbs.fullMul256_value product.r2 barrettMu0
  have hp11 := Challenge.EvmProof.Limbs.fullMul256_value product.r2 barrettMu1
  have hp12 := Challenge.EvmProof.Limbs.fullMul256_value product.r2 barrettMu2
  change partials.p00.value = product.r1.toNat * barrettMu0.toNat at hp00
  change partials.p01.value = product.r1.toNat * barrettMu1.toNat at hp01
  change partials.p02.value = product.r1.toNat * barrettMu2.toNat at hp02
  change partials.p10.value = product.r2.toNat * barrettMu0.toNat at hp10
  change partials.p11.value = product.r2.toNat * barrettMu1.toNat at hp11
  change partials.p12.value = product.r2.toNat * barrettMu2.toNat at hp12
  unfold Challenge.EvmProof.Limbs.WideProduct.value at hp00 hp01 hp02 hp10 hp11 hp12
  unfold Challenge.EvmProof.Limbs.WordSum.value at hl1 hl2value hl3value
  calc
    (product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
        barrettMu =
      product.r1.toNat * barrettMu0.toNat + Challenge.EvmProof.Limbs.radix *
        (product.r1.toNat * barrettMu1.toNat +
          product.r2.toNat * barrettMu0.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 2 *
          (product.r1.toNat * barrettMu2.toNat +
            product.r2.toNat * barrettMu1.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 3 *
          (product.r2.toNat * barrettMu2.toNat) := by
            unfold barrettMu
            ring
    _ = partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix *
          (partials.p00.hi.toNat + partials.p01.lo.toNat +
            partials.p10.lo.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 2 *
          (partials.p01.hi.toNat + partials.p10.hi.toNat +
            partials.p02.lo.toNat + partials.p11.lo.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 3 *
          (partials.p02.hi.toNat + partials.p11.hi.toNat +
            partials.p12.lo.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 4 * partials.p12.hi.toNat := by
          rw [← hp00, ← hp01, ← hp02, ← hp10, ← hp11, ← hp12]
          ring
    _ = partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix * l1.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 2 *
          (partials.p01.hi.toNat + partials.p10.hi.toNat +
            partials.p02.lo.toNat + partials.p11.lo.toNat + l1.carry.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 3 *
          (partials.p02.hi.toNat + partials.p11.hi.toNat +
            partials.p12.lo.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 4 * partials.p12.hi.toNat := by
          rw [← hl1]
          ring
    _ = partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix * l1.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 3 *
          (partials.p02.hi.toNat + partials.p11.hi.toNat +
            partials.p12.lo.toNat + l2.carry.toNat) +
        Challenge.EvmProof.Limbs.radix ^ 4 * partials.p12.hi.toNat := by
          rw [← hl2value]
          ring
    _ = partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix * l1.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 3 * l3.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 4 *
          (partials.p12.hi.toNat + l3.carry.toNat) := by
            rw [← hl3value]
            ring

theorem barrettQuotientTop_lt (product : SchoolbookProduct) :
    barrettQuotientTop product < Challenge.EvmProof.Limbs.radix := by
  let partials := barrettPartials product
  let l1 := barrettL1 partials
  let l2 := barrettL2 partials
  let l3 := barrettL3 partials
  have hreconstruct := barrettSchedule_value product
  dsimp only at hreconstruct
  change (product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
      barrettMu =
    partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix * l1.word.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat +
    Challenge.EvmProof.Limbs.radix ^ 3 * l3.word.toNat +
    Challenge.EvmProof.Limbs.radix ^ 4 *
      (partials.p12.hi.toNat + l3.carry.toNat) at hreconstruct
  have hr1 := product.r1.val.isLt
  have hr2 := product.r2.val.isLt
  change product.r1.toNat < Challenge.EvmProof.Limbs.radix at hr1
  change product.r2.toNat < Challenge.EvmProof.Limbs.radix at hr2
  have hinput : product.r1.toNat + Challenge.EvmProof.Limbs.radix *
      product.r2.toNat < Challenge.EvmProof.Limbs.radix ^ 2 := by nlinarith
  have hmu : barrettMu < Challenge.EvmProof.Limbs.radix ^ 3 := by
    norm_num [barrettMu, barrettMu0, barrettMu1, barrettMu2,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Limbs.radix]
  have hproduct := Nat.mul_lt_mul_of_lt_of_lt hinput hmu
  have htopLe : Challenge.EvmProof.Limbs.radix ^ 4 *
      (partials.p12.hi.toNat + l3.carry.toNat) ≤
      (product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
        barrettMu := by
    rw [hreconstruct]
    omega
  have hscaled : Challenge.EvmProof.Limbs.radix ^ 4 *
      (partials.p12.hi.toNat + l3.carry.toNat) <
      Challenge.EvmProof.Limbs.radix ^ 4 * Challenge.EvmProof.Limbs.radix := by
    have hpowEq : Challenge.EvmProof.Limbs.radix ^ 4 *
        Challenge.EvmProof.Limbs.radix = Challenge.EvmProof.Limbs.radix ^ 5 := by
      rw [← pow_succ]
    rw [hpowEq]
    exact htopLe.trans_lt hproduct
  have hpow : 0 < Challenge.EvmProof.Limbs.radix ^ 4 :=
    pow_pos Challenge.EvmProof.Limbs.radix_pos _
  have htop := (Nat.mul_lt_mul_left hpow).mp hscaled
  change partials.p12.hi.toNat + l3.carry.toNat <
    Challenge.EvmProof.Limbs.radix
  exact htop

theorem barrettQuotient_q1_value (product : SchoolbookProduct) :
    (barrettQuotient product).q1.toNat = barrettQuotientTop product := by
  let partials := barrettPartials product
  let l3 := barrettL3 partials
  have htop := barrettQuotientTop_lt product
  change partials.p12.hi.toNat + l3.carry.toNat <
    Challenge.EvmProof.Limbs.radix at htop
  change (partials.p12.hi + l3.carry).toNat = barrettQuotientTop product
  rw [Challenge.EvmProof.Word.word_toNat_add,
    show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
    Nat.mod_eq_of_lt htop]
  rfl

end Challenge.Bls12381.ProofSupport.Fp
