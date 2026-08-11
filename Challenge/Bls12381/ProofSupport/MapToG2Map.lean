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

end Challenge.Bls12381.ProofSupport.MapToG2
