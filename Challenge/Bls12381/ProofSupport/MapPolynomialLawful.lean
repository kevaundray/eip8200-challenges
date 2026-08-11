import Challenge.Bls12381.ProofSupport.MapPolynomial
import Mathlib.Tactic.FieldSimp

set_option warningAsError true

/-! # Lawful homogeneous polynomial evaluation -/

namespace Challenge.Bls12381.ProofSupport.MapPolynomial

variable {R : Type} [Field R]

/-- Homogeneous evaluation agrees with ordinary evaluation at `N / D`,
scaled by the expected denominator power. -/
theorem evalHom_eq_scaled_eval (coefficients : List R)
    (numerator denominator : R) (hcoefficients : coefficients ≠ [])
    (hdenominator : denominator ≠ 0) :
    evalHom coefficients numerator denominator =
      denominator ^ (coefficients.length - 1) *
        eval coefficients (numerator / denominator) := by
  induction coefficients with
  | nil => exact (hcoefficients rfl).elim
  | cons coefficient coefficients ih =>
      cases coefficients with
      | nil => simp [evalHom, eval]
      | cons next rest =>
          generalize hx : numerator / denominator = x at ih ⊢
          rw [evalHom]
          rw [ih (by simp)]
          simp only [List.length_cons, Nat.add_sub_cancel, eval]
          have hnumerator : denominator * x = numerator := by
            rw [← hx]
            field_simp
          rw [← hnumerator, pow_succ]
          ring

end Challenge.Bls12381.ProofSupport.MapPolynomial
