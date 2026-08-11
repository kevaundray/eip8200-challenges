import Mathlib.Tactic.Ring

set_option warningAsError true

/-! # Small constant-first polynomial evaluator for map-to-curve proofs -/

namespace Challenge.Bls12381.ProofSupport.MapPolynomial

variable {R : Type} [CommSemiring R]

/-- Evaluate a constant-first coefficient list. -/
def eval : List R → R → R
  | [], _ => 0
  | coefficient :: coefficients, x =>
      coefficient + x * eval coefficients x

/-- Homogeneous evaluation of a constant-first polynomial at `N / D`.
The result is the numerator after clearing `D ^ degree`. -/
def evalHom : List R → R → R → R
  | [], _, _ => 0
  | coefficient :: coefficients, numerator, denominator =>
      coefficient * denominator ^ coefficients.length +
        numerator * evalHom coefficients numerator denominator

/-- Coefficientwise addition, padding the shorter list with zeroes. -/
def add : List R → List R → List R
  | [], right => right
  | left, [] => left
  | a :: as, b :: bs => (a + b) :: add as bs

/-- Scale every coefficient. -/
def scale (a : R) : List R → List R
  | [] => []
  | b :: bs => (a * b) :: scale a bs

/-- Constant-first coefficient convolution. -/
def mul : List R → List R → List R
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, right => add (scale a right) (0 :: mul as right)

/-- Natural power under coefficient convolution. -/
def pow : List R → Nat → List R
  | _, 0 => [1]
  | coefficients, n + 1 => mul coefficients (pow coefficients n)

theorem eval_add (left right : List R) (x : R) :
    eval (add left right) x = eval left x + eval right x := by
  induction left generalizing right with
  | nil => simp [add, eval]
  | cons a as ih =>
      cases right with
      | nil => simp [add, eval]
      | cons b bs => simp [add, eval, ih]; ring

theorem eval_scale (a : R) (coefficients : List R) (x : R) :
    eval (scale a coefficients) x = a * eval coefficients x := by
  induction coefficients with
  | nil => simp [scale, eval]
  | cons b bs ih => simp [scale, eval, ih]; ring

theorem eval_mul (left right : List R) (x : R) :
    eval (mul left right) x = eval left x * eval right x := by
  induction left with
  | nil => simp [mul, eval]
  | cons a as ih =>
      cases right with
      | nil => simp [mul, eval]
      | cons b bs =>
          simp only [mul, eval_add, eval_scale, eval, ih]
          ring

theorem eval_pow (coefficients : List R) (exponent : Nat) (x : R) :
    eval (pow coefficients exponent) x = eval coefficients x ^ exponent := by
  induction exponent with
  | zero => simp [pow, eval]
  | succ exponent ih =>
      rw [pow, eval_mul, ih, pow_succ]
      exact mul_comm _ _

end Challenge.Bls12381.ProofSupport.MapPolynomial
