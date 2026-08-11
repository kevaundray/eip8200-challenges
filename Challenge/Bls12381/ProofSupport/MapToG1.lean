import Challenge.Bls12381.ProofSupport.FpSqrtLawful
import Mathlib.Tactic.Ring

set_option warningAsError true

/-!
# MAP_FP_TO_G1 shared arithmetic support

This module pins the source/RFC simplified-SWU constants and gives a
transparent projective SSWU program over the existing lawful base field.  The
square-root-ratio operation is an explicit parameter with a reusable contract;
the source exponentiation routine can refine that contract independently.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG1

abbrev Field := PrimeField.LawfulFp

/-- `A'` of the RFC 9380 G1 isogenous curve. -/
def isoA : Field :=
  0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D

/-- `B'` of the RFC 9380 G1 isogenous curve. -/
def isoB : Field :=
  0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0

/-- Source suite parameter `Z = 11`. -/
def isoZ : Field := 11

/-- Exact source `sqrt(-Z)` constant passed to `Fp.sqrtRatio`. -/
def sqrtMinusZ : Field :=
  0x04610E003BD3AC94DFA9246C390D7A78942602029175A4CA366D601F33F3946E3ED39794735C38315D874BC1D70637C3

/-- EIP/RFC effective G1 cofactor. -/
def hEff : Nat := 0xd201000000010001

theorem isoA_val : isoA.val =
    0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D := by
  rw [isoA, ZMod.val_ofNat]
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

theorem isoB_val : isoB.val =
    0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0 := by
  rw [isoB, ZMod.val_ofNat]
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

theorem sqrtMinusZ_square : sqrtMinusZ ^ 2 = -isoZ := by
  decide

theorem isoA_ne_zero : isoA ≠ 0 := by decide

theorem isoZ_ne_zero : isoZ ≠ 0 := by decide

/-- A ratio is square without introducing a partial division operation. -/
def IsSquareRatio (u v : Field) : Prop := ∃ y, y ^ 2 * v = u

/-- Contract required from the source square-root-ratio routine.  On failure
the returned root squares to `Z*u/v`, and failure is complete. -/
def SqrtRatioValid (u v : Field) (result : Bool × Field) : Prop :=
  if result.1 then result.2 ^ 2 * v = u
  else result.2 ^ 2 * v = isoZ * u ∧ ¬ IsSquareRatio u v

/-- Observable result of the exact source projective SSWU schedule. -/
structure SswuResult where
  xN : Field
  xD : Field
  y : Field
  denominatorExceptional : Bool
  sqrtWasQr : Bool

/-- Homogeneous membership on `y² = x³ + A'x + B'`, where `x=xN/xD`. -/
def ProjectiveOnCurve (point : SswuResult) : Prop :=
  point.y ^ 2 * point.xD ^ 3 =
    point.xN ^ 3 + isoA * point.xN * point.xD ^ 2 + isoB * point.xD ^ 3

private def signAdjusted (u y : Field) : Field :=
  if u.val % 2 = y.val % 2 then y else -y

private theorem signAdjusted_sq (u y : Field) : signAdjusted u y ^ 2 = y ^ 2 := by
  unfold signAdjusted
  split <;> ring

private theorem denominatorFactor_ne_zero (tv2 : Field) :
    isoA * (if tv2 = 0 then isoZ else -tv2) ≠ 0 := by
  apply mul_ne_zero isoA_ne_zero
  split
  · exact isoZ_ne_zero
  · exact neg_ne_zero.mpr ‹tv2 ≠ 0›

/-- The source CMOV makes the denominator cube passed to `sqrtRatio`
nonzero for every input. -/
theorem sswuDenominator_ne_zero (u : Field) :
    let tv1 := isoZ * u ^ 2
    let tv2 := tv1 ^ 2 + tv1
    let xD := isoA * if tv2 = 0 then isoZ else -tv2
    xD ^ 2 * xD ≠ 0 := by
  dsimp only
  apply mul_ne_zero
  · exact pow_ne_zero 2 (denominatorFactor_ne_zero _)
  · exact denominatorFactor_ne_zero _

/-- Exact decoded-field schedule of `MapFpToG1._sswuProjective`. -/
def sswuProjective
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) : SswuResult :=
  let tv1 := isoZ * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := isoB * (tv2 + 1)
  let exceptional := decide (tv2 = 0)
  let tv4 := isoA * if tv2 = 0 then isoZ else -tv2
  let tv2' := (tv3 ^ 2 + isoA * tv4 ^ 2) * tv3 +
    isoB * (tv4 ^ 2 * tv4)
  let tv6 := tv4 ^ 2 * tv4
  let ratio := sqrtRatio tv2' tv6
  let xNCandidate := tv1 * tv3
  let yCandidate := tv1 * u * ratio.2
  let xN := if ratio.1 then tv3 else xNCandidate
  let y0 := if ratio.1 then ratio.2 else yCandidate
  let y := signAdjusted u y0
  { xN, xD := tv4, y
    denominatorExceptional := exceptional
    sqrtWasQr := ratio.1 }

private theorem qr_projective (xN xD y : Field)
    (hy : y ^ 2 * (xD ^ 2 * xD) =
      (xN ^ 2 + isoA * xD ^ 2) * xN + isoB * (xD ^ 2 * xD)) :
    y ^ 2 * xD ^ 3 =
      xN ^ 3 + isoA * xN * xD ^ 2 + isoB * xD ^ 3 := by
  rw [show xD ^ 3 = xD ^ 2 * xD by ring]
  rw [hy]
  ring

private theorem nonqr_projective (u tv1 tv2 xN xD y : Field)
    (htv1 : tv1 = isoZ * u ^ 2)
    (htv2 : tv2 = tv1 ^ 2 + tv1)
    (hxN : xN = isoB * (tv2 + 1))
    (hxd : xD = isoA * -tv2)
    (hy : y ^ 2 * (xD ^ 2 * xD) = isoZ *
      ((xN ^ 2 + isoA * xD ^ 2) * xN + isoB * (xD ^ 2 * xD))) :
    (tv1 * u * y) ^ 2 * xD ^ 3 =
      (tv1 * xN) ^ 3 + isoA * (tv1 * xN) * xD ^ 2 +
        isoB * xD ^ 3 := by
  rw [show xD ^ 3 = xD ^ 2 * xD by ring]
  calc
    (tv1 * u * y) ^ 2 * (xD ^ 2 * xD) =
        tv1 ^ 2 * u ^ 2 * (y ^ 2 * (xD ^ 2 * xD)) := by ring
    _ = tv1 ^ 2 * u ^ 2 *
        (isoZ * ((xN ^ 2 + isoA * xD ^ 2) * xN +
          isoB * (xD ^ 2 * xD))) := by rw [hy]
    _ = (tv1 * xN) ^ 3 + isoA * (tv1 * xN) * xD ^ 2 +
        isoB * (xD ^ 2 * xD) := by
      rw [hxN, hxd, htv2, htv1]
      ring

/-- Fixed witness that the exceptional-denominator ratio is quadratic. -/
def exceptionalRoot : Field :=
  0x05BE3446F07E910E291153E84F1DABD3DFE5C2B1080D8B6A640425C3826F2A429373F9BAB7E8308F6DD10FFA11124DBC

private theorem exceptional_ratio_isSquare :
    let xN := isoB
    let xD := isoA * isoZ
    let numerator := (xN ^ 2 + isoA * xD ^ 2) * xN +
      isoB * (xD ^ 2 * xD)
    IsSquareRatio numerator (xD ^ 2 * xD) := by
  dsimp only
  refine ⟨exceptionalRoot, ?_⟩
  decide

/-- The exact projective SSWU schedule lands on the pinned isogenous curve
whenever its square-root-ratio dependency satisfies the source contract. -/
theorem sswuProjective_onCurve
    (sqrtRatio : Field → Field → Bool × Field)
    (hsqrt : ∀ u v, v ≠ 0 → SqrtRatioValid u v (sqrtRatio u v))
    (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) := by
  let tv1 := isoZ * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := isoB * (tv2 + 1)
  let tv4 := isoA * if tv2 = 0 then isoZ else -tv2
  let numerator := (tv3 ^ 2 + isoA * tv4 ^ 2) * tv3 +
    isoB * (tv4 ^ 2 * tv4)
  let denominator := tv4 ^ 2 * tv4
  generalize hratio : sqrtRatio numerator denominator = ratio
  rcases ratio with ⟨isQr, root⟩
  have hdenominator : denominator ≠ 0 := by
    simpa [tv1, tv2, tv4, denominator] using sswuDenominator_ne_zero u
  have hvalid := hsqrt numerator denominator hdenominator
  rw [hratio] at hvalid
  change (if isQr then root ^ 2 * denominator = numerator
    else root ^ 2 * denominator = isoZ * numerator ∧
      ¬ IsSquareRatio numerator denominator) at hvalid
  have hratio' : sqrtRatio
      ((tv3 ^ 2 + isoA * tv4 ^ 2) * tv3 + isoB * (tv4 ^ 2 * tv4))
      (tv4 ^ 2 * tv4) = (isQr, root) := by
    simpa [numerator, denominator] using hratio
  unfold ProjectiveOnCurve sswuProjective
  dsimp only
  rw [hratio']
  dsimp only
  change signAdjusted u (if isQr then root else tv1 * u * root) ^ 2 * tv4 ^ 3 =
    (if isQr then tv3 else tv1 * tv3) ^ 3 +
      isoA * (if isQr then tv3 else tv1 * tv3) * tv4 ^ 2 +
        isoB * tv4 ^ 3
  rw [signAdjusted_sq]
  cases isQr with
  | true =>
      simp only [if_true] at hvalid ⊢
      exact qr_projective tv3 tv4 root hvalid
  | false =>
      simp only [Bool.false_eq_true, if_false] at hvalid ⊢
      by_cases htv2 : tv2 = 0
      · have hexceptional : IsSquareRatio numerator denominator := by
          simpa [tv1, tv2, tv3, tv4, numerator, denominator, htv2] using
            exceptional_ratio_isSquare
        exact False.elim (hvalid.2 hexceptional)
      · exact nonqr_projective u tv1 tv2 tv3 tv4 root rfl rfl rfl
          (by simp [tv4, htv2]) hvalid.1

end Challenge.Bls12381.ProofSupport.MapToG1
