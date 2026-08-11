import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! Shared lawful-affine list-fold algorithms for multi-scalar multiplication. -/

namespace Challenge.Bls12381.ProofSupport.Msm

open EvmSemantics.Crypto.Bls12381

def foldG1 : G1Affine.Point → List (G1Affine.Point × Nat) →
    G1Affine.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG1 (G1Affine.add acc (ScalarMul.g1 scalar point)) rest

def g1 (terms : List (G1Affine.Point × Nat)) : G1Affine.Point :=
  foldG1 G1Affine.infinity terms

def foldG2 : G2Affine.Point → List (G2Affine.Point × Nat) →
    G2Affine.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG2 (G2Affine.add acc (ScalarMul.g2 scalar point)) rest

def g2 (terms : List (G2Affine.Point × Nat)) : G2Affine.Point :=
  foldG2 G2Affine.infinity terms

@[simp] theorem foldG1_nil (acc : G1Affine.Point) : foldG1 acc [] = acc := rfl

@[simp] theorem foldG1_cons (acc point : G1Affine.Point) (scalar : Nat)
    (rest : List (G1Affine.Point × Nat)) :
    foldG1 acc ((point, scalar) :: rest) =
      foldG1 (G1Affine.add acc (ScalarMul.g1 scalar point)) rest := rfl

theorem foldG1_append (acc : G1Affine.Point)
    (left right : List (G1Affine.Point × Nat)) :
    foldG1 acc (left ++ right) = foldG1 (foldG1 acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, foldG1_cons]
      exact ih _

@[simp] theorem foldG2_nil (acc : G2Affine.Point) : foldG2 acc [] = acc := rfl

@[simp] theorem foldG2_cons (acc point : G2Affine.Point) (scalar : Nat)
    (rest : List (G2Affine.Point × Nat)) :
    foldG2 acc ((point, scalar) :: rest) =
      foldG2 (G2Affine.add acc (ScalarMul.g2 scalar point)) rest := rfl

theorem foldG2_append (acc : G2Affine.Point)
    (left right : List (G2Affine.Point × Nat)) :
    foldG2 acc (left ++ right) = foldG2 (foldG2 acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, foldG2_cons]
      exact ih _

end Challenge.Bls12381.ProofSupport.Msm
