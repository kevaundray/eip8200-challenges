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

end Challenge.Bls12381.ProofSupport.MapToG1
