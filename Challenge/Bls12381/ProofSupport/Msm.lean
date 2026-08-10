import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! Shared projective list-fold algorithms for multi-scalar multiplication. -/

namespace Challenge.Bls12381.ProofSupport.Msm

open EvmSemantics.Crypto.Bls12381

def foldG1 : G1Projective.Point → List (G1Projective.Point × Nat) →
    G1Projective.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG1 (G1Projective.add acc (ScalarMul.g1 scalar point)) rest

def g1 (terms : List (G1Projective.Point × Nat)) : G1Projective.Point :=
  foldG1 G1Projective.infinity terms

def foldG2 : G2Projective.Point → List (G2Projective.Point × Nat) →
    G2Projective.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG2 (G2Projective.add acc (ScalarMul.g2 scalar point)) rest

def g2 (terms : List (G2Projective.Point × Nat)) : G2Projective.Point :=
  foldG2 G2Projective.infinity terms

@[simp] theorem foldG1_nil (acc : G1Projective.Point) : foldG1 acc [] = acc := rfl

@[simp] theorem foldG1_cons (acc point : G1Projective.Point) (scalar : Nat)
    (rest : List (G1Projective.Point × Nat)) :
    foldG1 acc ((point, scalar) :: rest) =
      foldG1 (G1Projective.add acc (ScalarMul.g1 scalar point)) rest := rfl

theorem foldG1_append (acc : G1Projective.Point)
    (left right : List (G1Projective.Point × Nat)) :
    foldG1 acc (left ++ right) = foldG1 (foldG1 acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, foldG1_cons]
      exact ih _

@[simp] theorem foldG2_nil (acc : G2Projective.Point) : foldG2 acc [] = acc := rfl

@[simp] theorem foldG2_cons (acc point : G2Projective.Point) (scalar : Nat)
    (rest : List (G2Projective.Point × Nat)) :
    foldG2 acc ((point, scalar) :: rest) =
      foldG2 (G2Projective.add acc (ScalarMul.g2 scalar point)) rest := rfl

theorem foldG2_append (acc : G2Projective.Point)
    (left right : List (G2Projective.Point × Nat)) :
    foldG2 acc (left ++ right) = foldG2 (foldG2 acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, foldG2_cons]
      exact ih _

/-- Affine semantic folds remain specifications, never executable algorithm
definitions. -/
def foldG1Spec : EvmSemantics.Crypto.Bls12381.Point →
    List (EvmSemantics.Crypto.Bls12381.Point × Nat) →
    EvmSemantics.Crypto.Bls12381.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG1Spec (EvmSemantics.Crypto.Bls12381.addPoint acc
        (ScalarMul.g1Spec scalar point)) rest

def foldG2Spec : EvmSemantics.Crypto.Bls12381.G2Point →
    List (EvmSemantics.Crypto.Bls12381.G2Point × Nat) →
    EvmSemantics.Crypto.Bls12381.G2Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG2Spec (EvmSemantics.Crypto.G2.addPoint acc
        (ScalarMul.g2Spec scalar point)) rest

end Challenge.Bls12381.ProofSupport.Msm
