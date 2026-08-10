import EvmSemantics.Crypto.Bls12381.Codec
import EvmSemantics.Crypto.Bls12381.G1Add
import EvmSemantics.Crypto.Bls12381.G2Add
import Challenge.EvmProof.Memory
import YulEvmCompiler.BytesLemmas
import Mathlib.Tactic.NormNum

set_option warningAsError true

/-!
# Shared EIP-2537 codecs

The challenge family uses the pinned semantics' codecs as its mathematical
wire format. This module gives those constants and operations one stable,
BLS-family-owned proof boundary.
-/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

abbrev decodeFp := EvmSemantics.Crypto.Bls12381Codec.decodeFp
abbrev decodeFp2 := EvmSemantics.Crypto.Bls12381Codec.decodeFp2
abbrev encodeFp := EvmSemantics.Crypto.Bls12381Codec.encodeFp
abbrev encodeFp2 := EvmSemantics.Crypto.Bls12381Codec.encodeFp2
abbrev decodeG1 := EvmSemantics.Crypto.Bls12381G1Add.decodePoint
abbrev encodeG1 := EvmSemantics.Crypto.Bls12381G1Add.encodePoint
abbrev decodeG2 := EvmSemantics.Crypto.Bls12381G2Add.decodePoint
abbrev encodeG2 := EvmSemantics.Crypto.Bls12381G2Add.encodePoint

def fpBytes : Nat := 64
def fp2Bytes : Nat := 128
def g1Bytes : Nat := 128
def g2Bytes : Nat := 256

@[simp] theorem encodeFp_size (a : Fp) : (encodeFp a).size = fpBytes := by
  exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _

@[simp] theorem encodeFp2_size (a : Fp2) : (encodeFp2 a).size = fp2Bytes := by
  unfold encodeFp2 EvmSemantics.Crypto.Bls12381Codec.encodeFp2
  simp [fp2Bytes, fpBytes]

@[simp] theorem encodeG1_size (point : Point) : (encodeG1 point).size = g1Bytes := by
  unfold encodeG1
  cases point <;>
    simp [EvmSemantics.Crypto.Bls12381G1Add.encodePoint, g1Bytes, fpBytes]

@[simp] theorem encodeG2_size (point : G2Point) : (encodeG2 point).size = g2Bytes := by
  unfold encodeG2
  cases point <;>
    simp [EvmSemantics.Crypto.Bls12381G2Add.encodePoint, g2Bytes, fp2Bytes]

@[simp] theorem fpBytes_eq_semantics :
    fpBytes = EvmSemantics.Crypto.Bls12381Codec.fpBytes := rfl

@[simp] theorem fp2Bytes_eq_semantics :
    fp2Bytes = EvmSemantics.Crypto.Bls12381Codec.fp2Bytes := rfl

@[simp] theorem g1Bytes_eq_semantics :
    g1Bytes = EvmSemantics.Crypto.Bls12381Codec.g1Bytes := rfl

@[simp] theorem g2Bytes_eq_semantics :
    g2Bytes = EvmSemantics.Crypto.Bls12381Codec.g2Bytes := rfl

theorem decodeFp_encodeFp (a : Fp) : decodeFp (encodeFp a) 0 = some a := by
  have hp : p < 256 ^ 48 := by norm_num [p, absU]
  have ha48 : a.val < 256 ^ 48 := a.isLt.trans hp
  have hsize : (EvmSemantics.Data.Bytes.natToBytesPadded a.val 64).size = 64 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have htop : ∀ i, i < 16 →
      (EvmSemantics.Data.Bytes.natToBytesPadded a.val 64)[i]! = 0 := by
    intro i hi
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem!]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 64 i
      (by omega)]
    have hexp : 48 ≤ 64 - 1 - i := by omega
    have hpow : 256 ^ 48 ≤ 256 ^ (64 - 1 - i) :=
      Nat.pow_le_pow_right (by omega) hexp
    rw [Nat.div_eq_of_lt (ha48.trans_le hpow)]
    rfl
  have htail :
      (EvmSemantics.Data.Bytes.natToBytesPadded a.val 64).extract 16 64 =
        EvmSemantics.Data.Bytes.natToBytesPadded a.val 48 := by
    apply ByteArray.ext_getElem
    · rw [ByteArray.size_extract, hsize]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      omega
    · intro i hiLeft hiRight
      have hi : i < 48 := by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at hiRight
        exact hiRight
      rw [ByteArray.getElem_extract]
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega)]
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiRight]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 64
        (16 + i) (by omega)]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 48 i
        hi]
      rw [show 64 - 1 - (16 + i) = 48 - 1 - i by omega]
  unfold decodeFp encodeFp EvmSemantics.Crypto.Bls12381Codec.decodeFp
    EvmSemantics.Crypto.Bls12381Codec.encodeFp
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes, hsize, gt_iff_lt,
    Nat.lt_irrefl, ↓reduceIte, Nat.zero_add]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  norm_num [List.range', htop, htail]
  rw [Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded _ 48 ha48]
  exact ⟨a.isLt, by apply Fin.ext; simp⟩

/-- Decoding is local to its 64-byte window.  This framed form is the reusable
lemma needed by all larger EIP-2537 codecs. -/
theorem decodeFp_framed (pre suffix : ByteArray) (a : Fp) :
    decodeFp (pre ++ encodeFp a ++ suffix) pre.size = some a := by
  have hp : p < 256 ^ 48 := by norm_num [p, absU]
  have ha48 : a.val < 256 ^ 48 := a.isLt.trans hp
  let encoded := encodeFp a
  let input := pre ++ encoded ++ suffix
  have hencodedSize : encoded.size = 64 := by
    exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hinputSize : input.size = pre.size + 64 + suffix.size := by
    simp [input, hencodedSize]
  have hbyte : ∀ i, i < 64 →
      input[pre.size + i]?.getD 0 = encoded[i]?.getD 0 := by
    intro i hi
    simp only [input, Challenge.EvmProof.Memory.getElem?_getD_append]
    rw [if_pos (by simp [hencodedSize]; omega)]
    rw [if_neg (by omega)]
    congr 2
    omega
  have htop : ∀ i, i < 16 → input[pre.size + i]! = 0 := by
    intro i hi
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem!]
    rw [hbyte i (by omega)]
    change
      (EvmSemantics.Data.Bytes.natToBytesPadded a.val 64)[i]?.getD 0 = 0
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 64 i
      (by omega)]
    have hexp : 48 ≤ 64 - 1 - i := by omega
    have hpow : 256 ^ 48 ≤ 256 ^ (64 - 1 - i) :=
      Nat.pow_le_pow_right (by omega) hexp
    rw [Nat.div_eq_of_lt (ha48.trans_le hpow)]
    rfl
  have htop0 : input[pre.size]! = 0 := by
    simpa using htop 0 (by omega)
  have htail :
      input.extract (pre.size + 16) (pre.size + 64) =
        EvmSemantics.Data.Bytes.natToBytesPadded a.val 48 := by
    apply ByteArray.ext_getElem
    · rw [ByteArray.size_extract]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      omega
    · intro i hiLeft hiRight
      have hi : i < 48 := by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at hiRight
        exact hiRight
      rw [ByteArray.getElem_extract]
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiRight]
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
        rw [hinputSize]
        omega)]
      rw [show pre.size + 16 + i = pre.size + (16 + i) by omega]
      rw [hbyte (16 + i) (by omega)]
      change
        (EvmSemantics.Data.Bytes.natToBytesPadded a.val 64)[16 + i]?.getD 0 = _
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 64
        (16 + i) (by omega)]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 48 i hi]
      rw [show 64 - 1 - (16 + i) = 48 - 1 - i by omega]
  change EvmSemantics.Crypto.Bls12381Codec.decodeFp input pre.size = some a
  unfold EvmSemantics.Crypto.Bls12381Codec.decodeFp
  rw [if_neg (by simp [EvmSemantics.Crypto.Bls12381Codec.fpBytes, hinputSize])]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  norm_num [List.range', htop, htop0, htail]
  rw [Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded _ 48 ha48]
  exact ⟨a.isLt, by apply Fin.ext; simp⟩

theorem decodeFp_eq_none_of_short {input : ByteArray} {offset : Nat}
    (hshort : input.size < offset + fpBytes) : decodeFp input offset = none := by
  change input.size < offset + 64 at hshort
  unfold decodeFp EvmSemantics.Crypto.Bls12381Codec.decodeFp
  rw [if_pos (by
    simpa [EvmSemantics.Crypto.Bls12381Codec.fpBytes] using hshort)]

theorem decodeFp_first (a b : Fp) :
    decodeFp (encodeFp a ++ encodeFp b) 0 = some a := by
  simpa using decodeFp_framed ByteArray.empty (encodeFp b) a

theorem decodeFp_second (a b : Fp) :
    decodeFp (encodeFp a ++ encodeFp b) fpBytes = some b := by
  simpa [fpBytes] using decodeFp_framed (encodeFp a) ByteArray.empty b

theorem decodeFp2_encodeFp2 (a : Fp2) :
    decodeFp2 (encodeFp2 a) 0 = some a := by
  unfold decodeFp2 encodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
    EvmSemantics.Crypto.Bls12381Codec.encodeFp2
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes, Nat.zero_add]
  have h0 : EvmSemantics.Crypto.Bls12381Codec.decodeFp
      (EvmSemantics.Crypto.Bls12381Codec.encodeFp a.c0 ++
        EvmSemantics.Crypto.Bls12381Codec.encodeFp a.c1) 0 = some a.c0 :=
    decodeFp_first a.c0 a.c1
  have h1 : EvmSemantics.Crypto.Bls12381Codec.decodeFp
      (EvmSemantics.Crypto.Bls12381Codec.encodeFp a.c0 ++
        EvmSemantics.Crypto.Bls12381Codec.encodeFp a.c1) 64 = some a.c1 := by
    simpa [fpBytes] using decodeFp_second a.c0 a.c1
  rw [h0, h1]

theorem decodeFp2_first (a b : Fp2) :
    decodeFp2 (encodeFp2 a ++ encodeFp2 b) 0 = some a := by
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  have h0 := decodeFp_framed ByteArray.empty
    (encodeFp a.c1 ++ encodeFp2 b) a.c0
  have h1 := decodeFp_framed (encodeFp a.c0) (encodeFp2 b) a.c1
  change EvmSemantics.Crypto.Bls12381Codec.decodeFp _ 0 = some a.c0 at h0
  rw [encodeFp_size] at h1
  change EvmSemantics.Crypto.Bls12381Codec.decodeFp _ 64 = some a.c1 at h1
  have hfirst : EvmSemantics.Crypto.Bls12381Codec.decodeFp
      (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 a ++
        EvmSemantics.Crypto.Bls12381Codec.encodeFp2 b) 0 = some a.c0 := by
    simpa only [decodeFp, encodeFp, encodeFp2,
      EvmSemantics.Crypto.Bls12381Codec.encodeFp2,
      ByteArray.empty_append, ByteArray.append_assoc] using h0
  have hsecond : EvmSemantics.Crypto.Bls12381Codec.decodeFp
      (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 a ++
        EvmSemantics.Crypto.Bls12381Codec.encodeFp2 b) 64 = some a.c1 := by
    simpa only [decodeFp, encodeFp, encodeFp2,
      EvmSemantics.Crypto.Bls12381Codec.encodeFp2,
      ByteArray.append_assoc, encodeFp_size] using h1
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes, Nat.zero_add]
  rw [hfirst, hsecond]

theorem decodeFp2_second (a b : Fp2) :
    decodeFp2 (encodeFp2 a ++ encodeFp2 b) fp2Bytes = some b := by
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  have h0 := decodeFp_framed (encodeFp2 a) (encodeFp b.c1) b.c0
  have h1 := decodeFp_framed (encodeFp2 a ++ encodeFp b.c0)
    ByteArray.empty b.c1
  rw [encodeFp2_size] at h0
  change EvmSemantics.Crypto.Bls12381Codec.decodeFp _ 128 = some b.c0 at h0
  rw [ByteArray.size_append, encodeFp2_size, encodeFp_size] at h1
  change EvmSemantics.Crypto.Bls12381Codec.decodeFp _ 192 = some b.c1 at h1
  have hfirst : EvmSemantics.Crypto.Bls12381Codec.decodeFp
      (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 a ++
        EvmSemantics.Crypto.Bls12381Codec.encodeFp2 b) 128 = some b.c0 := by
    simpa only [decodeFp, encodeFp, encodeFp2,
      EvmSemantics.Crypto.Bls12381Codec.encodeFp2, fp2Bytes,
      encodeFp2_size, ByteArray.append_assoc] using h0
  have hsecond : EvmSemantics.Crypto.Bls12381Codec.decodeFp
      (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 a ++
        EvmSemantics.Crypto.Bls12381Codec.encodeFp2 b) 192 = some b.c1 := by
    simpa only [decodeFp, encodeFp, encodeFp2,
      EvmSemantics.Crypto.Bls12381Codec.encodeFp2,
      encodeFp2_size, encodeFp_size, ByteArray.append_empty,
      ByteArray.append_assoc] using h1
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes, fp2Bytes]
  rw [hfirst, show 128 + 64 = 192 by norm_num, hsecond]

/-- A semantic G1 point is wire-valid when it is infinity or its affine
coordinates satisfy the BLS12-381 curve equation. -/
def ValidG1 : Point → Prop
  | .infinity => True
  | .affine x y => EvmSemantics.Crypto.Bls12381.onCurve x y = true

/-- A semantic G2 point is wire-valid when it is infinity or its affine
coordinates satisfy the BLS12-381 twist equation. -/
def ValidG2 : G2Point → Prop
  | .infinity => True
  | .affine x y =>
      EvmSemantics.Crypto.G2.onCurve
        EvmSemantics.Crypto.Bls12381.g2Curve x y = true

theorem decodeG1_encodeG1 (point : Point) (hpoint : ValidG1 point) :
    decodeG1 (encodeG1 point) 0 = some point := by
  cases point with
  | infinity =>
      unfold decodeG1 encodeG1 EvmSemantics.Crypto.Bls12381G1Add.decodePoint
        EvmSemantics.Crypto.Bls12381G1Add.encodePoint
      simp only
      have hx : EvmSemantics.Crypto.Bls12381Codec.decodeFp
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp 0 ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp 0) 0 = some 0 :=
        decodeFp_first 0 0
      have hy : EvmSemantics.Crypto.Bls12381Codec.decodeFp
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp 0 ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp 0) 64 = some 0 := by
        simpa [fpBytes] using decodeFp_second 0 0
      rw [hx, show 0 + EvmSemantics.Crypto.Bls12381Codec.fpBytes = 64 by rfl,
        hy]
      rfl
  | affine x y =>
      change EvmSemantics.Crypto.Bls12381.onCurve x y = true at hpoint
      have hnotzero : ¬(x.val = 0 ∧ y.val = 0) := by
        rintro ⟨hx, hy⟩
        have hx0 : x = 0 := Fin.ext hx
        have hy0 : y = 0 := Fin.ext hy
        subst x
        subst y
        have hzeroCurve :
            EvmSemantics.Crypto.Bls12381.onCurve 0 0 = false := by decide
        rw [hzeroCurve] at hpoint
        exact Bool.noConfusion hpoint
      unfold decodeG1 encodeG1 EvmSemantics.Crypto.Bls12381G1Add.decodePoint
        EvmSemantics.Crypto.Bls12381G1Add.encodePoint
      simp only
      have hx : EvmSemantics.Crypto.Bls12381Codec.decodeFp
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp x ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp y) 0 = some x :=
        decodeFp_first x y
      have hy : EvmSemantics.Crypto.Bls12381Codec.decodeFp
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp x ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp y) 64 = some y := by
        simpa [fpBytes] using decodeFp_second x y
      rw [hx, show 0 + EvmSemantics.Crypto.Bls12381Codec.fpBytes = 64 by rfl,
        hy]
      have hxy : x = 0 → y ≠ 0 := by
        intro hx0 hy0
        apply hnotzero
        simp [hx0, hy0]
      simp [hpoint]
      exact hxy

theorem decodeG2_encodeG2 (point : G2Point) (hpoint : ValidG2 point) :
    decodeG2 (encodeG2 point) 0 = some point := by
  cases point with
  | infinity =>
      unfold decodeG2 encodeG2 EvmSemantics.Crypto.Bls12381G2Add.decodePoint
        EvmSemantics.Crypto.Bls12381G2Add.encodePoint
      simp only
      have hx : EvmSemantics.Crypto.Bls12381Codec.decodeFp2
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 0 ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp2 0) 0 = some 0 :=
        decodeFp2_first 0 0
      have hy : EvmSemantics.Crypto.Bls12381Codec.decodeFp2
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 0 ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp2 0) 128 = some 0 := by
        simpa [fp2Bytes] using decodeFp2_second 0 0
      rw [hx, show 0 + EvmSemantics.Crypto.Bls12381Codec.fp2Bytes = 128 by rfl,
        hy]
      rfl
  | affine x y =>
      change EvmSemantics.Crypto.G2.onCurve
        EvmSemantics.Crypto.Bls12381.g2Curve x y = true at hpoint
      have hnotzero : ¬(x.c0.val = 0 ∧ x.c1.val = 0 ∧
          y.c0.val = 0 ∧ y.c1.val = 0) := by
        rintro ⟨hx0, hx1, hy0, hy1⟩
        have hxc0 : x.c0 = 0 := Fin.ext hx0
        have hxc1 : x.c1 = 0 := Fin.ext hx1
        have hyc0 : y.c0 = 0 := Fin.ext hy0
        have hyc1 : y.c1 = 0 := Fin.ext hy1
        cases x
        cases y
        simp only at hxc0 hxc1 hyc0 hyc1
        subst_vars
        have hzeroCurve : EvmSemantics.Crypto.G2.onCurve
            EvmSemantics.Crypto.Bls12381.g2Curve
            ({ c0 := 0, c1 := 0 } : Fp2)
            ({ c0 := 0, c1 := 0 } : Fp2) = false := by decide
        rw [hzeroCurve] at hpoint
        exact Bool.noConfusion hpoint
      unfold decodeG2 encodeG2 EvmSemantics.Crypto.Bls12381G2Add.decodePoint
        EvmSemantics.Crypto.Bls12381G2Add.encodePoint
      simp only
      have hx : EvmSemantics.Crypto.Bls12381Codec.decodeFp2
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 x ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp2 y) 0 = some x :=
        decodeFp2_first x y
      have hy : EvmSemantics.Crypto.Bls12381Codec.decodeFp2
          (EvmSemantics.Crypto.Bls12381Codec.encodeFp2 x ++
            EvmSemantics.Crypto.Bls12381Codec.encodeFp2 y) 128 = some y := by
        simpa [fp2Bytes] using decodeFp2_second x y
      rw [hx, show 0 + EvmSemantics.Crypto.Bls12381Codec.fp2Bytes = 128 by rfl,
        hy]
      have hxy : x.c0 = 0 → x.c1 = 0 → y.c0 = 0 → y.c1 ≠ 0 := by
        intro hx0 hx1 hy0 hy1
        apply hnotzero
        simp [hx0, hx1, hy0, hy1]
      simp [hpoint]
      exact hxy

end Challenge.Bls12381.ProofSupport.Codec
