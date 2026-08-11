import Challenge.Bls12381.ProofSupport.MapToG2Executable
import Challenge.Bls12381.ProofSupport.MapToG2IsogenyLawful
import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! # Shared lawful MAP_FP2_TO_G2 operation -/

namespace Challenge.Bls12381.ProofSupport.MapToG2

theorem mapBeforeCofactor_onCurve (u : Field) :
    G2Affine.OnCurve (mapBeforeCofactor u) := by
  rw [mapBeforeCofactor_eq]
  exact iso3_onCurve _ _ _ (sourceSswu_onCurve u)

theorem map_onCurve (u : Field) : G2Affine.OnCurve (map u) := by
  rw [map_eq]
  exact ScalarMul.g2_onCurve hEff (mapBeforeCofactor u)
    (mapBeforeCofactor_onCurve u)

/-- The lawful map always converts to a codec-valid decoded G2 point. -/
theorem map_toWire_valid (u : Field) :
    Codec.ValidG2 (G2Affine.toWire (map u)) := by
  have hcurve := map_onCurve u
  cases hpoint : map u with
  | infinity => trivial
  | affine x y =>
      exact G2Affine.onCurve_toWire (by simpa [hpoint] using hcurve)

theorem run_eq_some_iff (input output : ByteArray) :
    run input = some output ↔
      ∃ u, input.size = Codec.fp2Bytes ∧ Codec.decodeFp2 input 0 = some u ∧
        output = Codec.encodeG2
          (G2Affine.toWire (map (LawfulFp2.ofWire u))) := by
  simp [run]
  intro _
  cases hdecode : Codec.decodeFp2 input 0 with
  | none => simp
  | some u => simp [eq_comm]

theorem run_eq_none_of_wrong_length {input : ByteArray}
    (hsize : input.size ≠ Codec.fp2Bytes) : run input = none := by
  have hsize' : input.size ≠ 128 := by simpa [Codec.fp2Bytes] using hsize
  simp [run, Codec.fp2Bytes, hsize']

theorem run_eq_none_of_first_padding_nonzero
    {input : ByteArray} {i : Nat}
    (hsize : input.size = Codec.fp2Bytes) (hi : i < 16)
    (hnonzero : input[i]! ≠ 0) : run input = none := by
  have hdecode : Codec.decodeFp2 input 0 = none :=
    Codec.decodeFp2_eq_none_of_first_padding_nonzero
      (offset := 0) (by simp [hsize]) hi (by simpa using hnonzero)
  simp [run, hsize, hdecode]

theorem run_eq_none_of_second_padding_nonzero
    {input : ByteArray} {i : Nat}
    (hsize : input.size = Codec.fp2Bytes) (hi : i < 16)
    (hnonzero : input[Codec.fpBytes + i]! ≠ 0) : run input = none := by
  have hdecode : Codec.decodeFp2 input 0 = none :=
    Codec.decodeFp2_eq_none_of_second_padding_nonzero
      (offset := 0) (by simp [hsize]) hi (by simpa using hnonzero)
  simp [run, hsize, hdecode]

theorem run_eq_none_of_first_value_ge {input : ByteArray}
    (hsize : input.size = Codec.fp2Bytes)
    (hvalue : EvmSemantics.Crypto.Bls12381.p ≤
      Codec.fpWindowValue input 0) : run input = none := by
  have hdecode : Codec.decodeFp2 input 0 = none :=
    Codec.decodeFp2_eq_none_of_first_value_ge
      (offset := 0) (by simp [hsize]) hvalue
  simp [run, hsize, hdecode]

theorem run_eq_none_of_second_value_ge {input : ByteArray}
    (hsize : input.size = Codec.fp2Bytes)
    (hvalue : EvmSemantics.Crypto.Bls12381.p ≤
      Codec.fpWindowValue input Codec.fpBytes) : run input = none := by
  have hdecode : Codec.decodeFp2 input 0 = none :=
    Codec.decodeFp2_eq_none_of_second_value_ge
      (offset := 0) (by simp [hsize]) (by simpa using hvalue)
  simp [run, hsize, hdecode]

end Challenge.Bls12381.ProofSupport.MapToG2
