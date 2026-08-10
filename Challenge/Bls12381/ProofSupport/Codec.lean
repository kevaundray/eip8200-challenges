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

end Challenge.Bls12381.ProofSupport.Codec
