import Challenge.Bls12381.ProofSupport.LawfulFp2
import Mathlib.Tactic.Ring

set_option warningAsError true

/-!
# MAP_FP2_TO_G2 shared arithmetic support

This module pins the source/RFC simplified-SWU constants and gives a
transparent projective SSWU program over the existing lawful quadratic
field. The square-root-ratio operation remains an explicit dependency with a
non-vacuous contract; its source implementation is refined separately.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG2

abbrev Field := LawfulFp2.Carrier

/-- `A' = 240 * i` of the RFC 9380 G2 isogenous curve. -/
def isoA : Field := ⟨0, 240⟩

/-- `B' = 1012 * (1 + i)` of the RFC 9380 G2 isogenous curve. -/
def isoB : Field := ⟨1012, 1012⟩

/-- Source suite parameter `Z = -(2 + i)`. -/
def isoZ : Field := ⟨-2, -1⟩

/-- Exact RFC effective G2 cofactor. -/
def hEff : Nat :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551

theorem isoA_ne_zero : isoA ≠ 0 := by decide

theorem isoZ_ne_zero : isoZ ≠ 0 := by decide

/-- A ratio is square without introducing partial division. -/
def IsSquareRatio (u v : Field) : Prop := ∃ y, y ^ 2 * v = u

/-- Contract required from the source Fp2 square-root-ratio routine. -/
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

/-- Homogeneous membership on `y² = x³ + A'x + B'`, with `x=xN/xD`. -/
def ProjectiveOnCurve (point : SswuResult) : Prop :=
  point.y ^ 2 * point.xD ^ 3 =
    point.xN ^ 3 + isoA * point.xN * point.xD ^ 2 + isoB * point.xD ^ 3

/-- RFC Fp2 sign: sign of c0, except zero c0 defers to c1. -/
def sourceSgn0 (a : Field) : Nat :=
  if a.re.val = 0 then a.im.val % 2 else a.re.val % 2

/-- Exact source sign selection at the lawful decoded-field boundary. -/
def sourceSignAdjusted (u y : Field) : Field :=
  if sourceSgn0 u = sourceSgn0 y then y else -y

private theorem sourceSignAdjusted_sq (u y : Field) :
    sourceSignAdjusted u y ^ 2 = y ^ 2 := by
  unfold sourceSignAdjusted
  split <;> ring

private theorem denominatorFactor_ne_zero (tv2 : Field) :
    isoA * (if tv2 = 0 then isoZ else -tv2) ≠ 0 := by
  apply mul_ne_zero isoA_ne_zero
  split
  · exact isoZ_ne_zero
  · exact neg_ne_zero.mpr ‹tv2 ≠ 0›

/-- The source CMOV makes the denominator cube passed to Fp2 sqrtRatio
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

/-- Exact decoded-field schedule of `MapFpToG2._sswuProjective`. -/
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
  let y := sourceSignAdjusted u y0
  { xN, xD := tv4, y
    denominatorExceptional := exceptional
    sqrtWasQr := ratio.1 }

/-- Unsigned y candidate immediately before the source sign CMOV. -/
def sswuSourceY0
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) : Field :=
  let tv1 := isoZ * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := isoB * (tv2 + 1)
  let tv4 := isoA * if tv2 = 0 then isoZ else -tv2
  let numerator := (tv3 ^ 2 + isoA * tv4 ^ 2) * tv3 +
    isoB * (tv4 ^ 2 * tv4)
  let denominator := tv4 ^ 2 * tv4
  let ratio := sqrtRatio numerator denominator
  if ratio.1 then ratio.2 else tv1 * u * ratio.2

theorem sswuProjective_y_eq_source
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) :
    (sswuProjective sqrtRatio u).y =
      sourceSignAdjusted u (sswuSourceY0 sqrtRatio u) := by
  rfl

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

/-- Fixed root of the exceptional-input SSWU ratio. -/
def exceptionalRoot : Field :=
  ⟨3611395798403580372189180981549434777847917790633063236702417299179272465463714843962369288472002469087378085294992,
   423613093348586218576377851437437729690830432842722856441196780662664494552025968214749014884639894158037286276385⟩

private theorem exceptional_ratio_isSquare :
    let xN := isoB
    let xD := isoA * isoZ
    let numerator := (xN ^ 2 + isoA * xD ^ 2) * xN +
      isoB * (xD ^ 2 * xD)
    IsSquareRatio numerator (xD ^ 2 * xD) := by
  dsimp only
  refine ⟨exceptionalRoot, ?_⟩
  decide

/-- Numerator passed by the source SSWU schedule to Fp2 sqrtRatio. -/
def sswuNumerator (u : Field) : Field :=
  let tv1 := isoZ * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := isoB * (tv2 + 1)
  let tv4 := isoA * if tv2 = 0 then isoZ else -tv2
  (tv3 ^ 2 + isoA * tv4 ^ 2) * tv3 + isoB * (tv4 ^ 2 * tv4)

/-- Nonzero denominator passed by the source SSWU schedule to Fp2 sqrtRatio. -/
def sswuDenominator (u : Field) : Field :=
  let tv1 := isoZ * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv4 := isoA * if tv2 = 0 then isoZ else -tv2
  tv4 ^ 2 * tv4

theorem sswuProjective_onCurve_of_valid
    (sqrtRatio : Field → Field → Bool × Field)
    (u : Field)
    (hvalidAt : SqrtRatioValid (sswuNumerator u) (sswuDenominator u)
      (sqrtRatio (sswuNumerator u) (sswuDenominator u))) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) := by
  let tv1 := isoZ * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := isoB * (tv2 + 1)
  let tv4 := isoA * if tv2 = 0 then isoZ else -tv2
  let numerator := (tv3 ^ 2 + isoA * tv4 ^ 2) * tv3 +
    isoB * (tv4 ^ 2 * tv4)
  let denominator := tv4 ^ 2 * tv4
  have hvalid : SqrtRatioValid numerator denominator
      (sqrtRatio numerator denominator) := by
    simpa [sswuNumerator, sswuDenominator, tv1, tv2, tv3, tv4,
      numerator, denominator] using hvalidAt
  generalize hratio : sqrtRatio numerator denominator = ratio
  rcases ratio with ⟨isQr, root⟩
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
  change sourceSignAdjusted u
      (if isQr then root else tv1 * u * root) ^ 2 * tv4 ^ 3 =
    (if isQr then tv3 else tv1 * tv3) ^ 3 +
      isoA * (if isQr then tv3 else tv1 * tv3) * tv4 ^ 2 +
        isoB * tv4 ^ 3
  rw [sourceSignAdjusted_sq]
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

theorem sswuProjective_onCurve
    (sqrtRatio : Field → Field → Bool × Field)
    (hsqrt : ∀ u v, v ≠ 0 → SqrtRatioValid u v (sqrtRatio u v))
    (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) := by
  apply sswuProjective_onCurve_of_valid sqrtRatio u
  apply hsqrt
  simpa [sswuDenominator] using sswuDenominator_ne_zero u

end Challenge.Bls12381.ProofSupport.MapToG2
