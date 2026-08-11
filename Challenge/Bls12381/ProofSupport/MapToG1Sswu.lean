import Challenge.Bls12381.ProofSupport.MapToG1SqrtRatio

set_option warningAsError true

/-! # Source G1 simplified SWU refinement -/

namespace Challenge.Bls12381.ProofSupport.MapToG1

/-- The source square-root-ratio implementation discharges the SSWU
dependency, yielding an unconditional projective on-curve theorem. -/
theorem sswuSource_onCurve (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatioSource u) := by
  apply sswuProjective_onCurve_of_valid sqrtRatioSource u
  generalize hnumerator : sswuNumerator u = numerator
  generalize hdenominator : sswuDenominator u = denominator
  have hdenominator' : denominator ≠ 0 := by
    rw [← hdenominator]
    simpa [sswuDenominator] using sswuDenominator_ne_zero u
  have hvalid : SqrtRatioValid numerator denominator
      (sqrtRatioSource numerator denominator) :=
    sqrtRatioSource_valid numerator denominator hdenominator'
  exact hvalid

end Challenge.Bls12381.ProofSupport.MapToG1
