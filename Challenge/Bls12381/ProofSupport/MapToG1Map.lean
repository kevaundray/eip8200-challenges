import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.MapToG1IsogenyLawful
import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! # Shared lawful MAP_FP_TO_G1 operation -/

namespace Challenge.Bls12381.ProofSupport.MapToG1

/-- Source SSWU followed by the pole-aware lawful 11-isogeny. -/
def mapBeforeCofactor (u : Field) : G1Affine.Point :=
  let mapped := sswuProjective sqrtRatioSource u
  iso11 mapped.xN mapped.xD mapped.y

/-- First-milestone proof-friendly map: source SSWU, lawful 11-isogeny, then
naive binary multiplication by the exact RFC effective cofactor. -/
def map (u : Field) : G1Affine.Point :=
  ScalarMul.g1 hEff (mapBeforeCofactor u)

theorem mapBeforeCofactor_onCurve (u : Field) :
    G1Affine.OnCurve (mapBeforeCofactor u) := by
  apply iso11_onCurve
  exact sswuSource_onCurve u

theorem map_onCurve (u : Field) : G1Affine.OnCurve (map u) := by
  exact ScalarMul.g1_onCurve hEff (mapBeforeCofactor u)
    (mapBeforeCofactor_onCurve u)

/-- The lawful map always converts to a codec-valid decoded G1 point. -/
theorem map_toWire_valid (u : Field) :
    Codec.ValidG1 (G1Affine.toWire (map u)) := by
  have hcurve := map_onCurve u
  cases hpoint : map u with
  | infinity => trivial
  | affine x y =>
      exact G1Affine.onCurve_toWire (by simpa [hpoint] using hcurve)

/-- Exact shared EIP-2537 decoded-value adapter. The outer size check is
deliberate: the field codec is framed and therefore also accepts a valid
64-byte window inside a larger byte array, whereas the precompile input must
be exactly one 64-byte field element. -/
def run (input : ByteArray) : Option ByteArray := do
  if input.size ≠ Codec.fpBytes then none
  let u ← Codec.decodeFp input 0
  pure (Codec.encodeG1 (G1Affine.toWire (map (PrimeField.finEquiv u))))

theorem run_eq_some_iff (input output : ByteArray) :
    run input = some output ↔
      ∃ u, input.size = Codec.fpBytes ∧ Codec.decodeFp input 0 = some u ∧
        output = Codec.encodeG1 (G1Affine.toWire (map (PrimeField.finEquiv u))) := by
  simp [run]
  intro _
  cases hdecode : Codec.decodeFp input 0 with
  | none => simp
  | some u => simp [eq_comm]

theorem run_eq_none_of_wrong_length {input : ByteArray}
    (hsize : input.size ≠ Codec.fpBytes) : run input = none := by
  have hsize' : input.size ≠ 64 := by simpa [Codec.fpBytes] using hsize
  simp [run, Codec.fpBytes, hsize']

theorem run_eq_none_of_padding_nonzero {input : ByteArray} {i : Nat}
    (hsize : input.size = Codec.fpBytes) (hi : i < 16)
    (hnonzero : input[i]! ≠ 0) : run input = none := by
  have hdecode : Codec.decodeFp input 0 = none :=
    Codec.decodeFp_eq_none_of_padding_nonzero
      (offset := 0) (by simp [hsize]) hi (by simpa using hnonzero)
  simp [run, hsize, hdecode]

theorem run_eq_none_of_value_ge {input : ByteArray}
    (hsize : input.size = Codec.fpBytes)
    (hvalue : EvmSemantics.Crypto.Bls12381.p ≤ Codec.fpWindowValue input 0) :
    run input = none := by
  have hdecode : Codec.decodeFp input 0 = none :=
    Codec.decodeFp_eq_none_of_value_ge
      (offset := 0) (by simp [hsize]) hvalue
  simp [run, hsize, hdecode]

end Challenge.Bls12381.ProofSupport.MapToG1
