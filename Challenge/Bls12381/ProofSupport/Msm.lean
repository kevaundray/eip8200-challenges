import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! Shared list-fold specification for multi-scalar multiplication. -/

namespace Challenge.Bls12381.ProofSupport.Msm

open EvmSemantics.Crypto.Bls12381

def fold : EvmSemantics.Crypto.Bls12381.Point →
    List (EvmSemantics.Crypto.Bls12381.Point × Nat) →
    EvmSemantics.Crypto.Bls12381.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      fold (EvmSemantics.Crypto.Bls12381.addPoint acc
        (ScalarMul.fold scalar point)) rest

@[simp] theorem fold_nil (acc : EvmSemantics.Crypto.Bls12381.Point) :
    fold acc [] = acc := rfl

@[simp] theorem fold_cons (acc point : EvmSemantics.Crypto.Bls12381.Point)
    (scalar : Nat) (rest : List (EvmSemantics.Crypto.Bls12381.Point × Nat)) :
    fold acc ((point, scalar) :: rest) =
      fold (EvmSemantics.Crypto.Bls12381.addPoint acc
        (ScalarMul.fold scalar point)) rest := rfl

theorem fold_append (acc : EvmSemantics.Crypto.Bls12381.Point)
    (left right : List (EvmSemantics.Crypto.Bls12381.Point × Nat)) :
    fold acc (left ++ right) = fold (fold acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, fold_cons]
      exact ih _

def foldG2 : EvmSemantics.Crypto.Bls12381.G2Point →
    List (EvmSemantics.Crypto.Bls12381.G2Point × Nat) →
    EvmSemantics.Crypto.Bls12381.G2Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG2 (EvmSemantics.Crypto.G2.addPoint acc
        (ScalarMul.foldG2 scalar point)) rest

theorem foldG2_append (acc : EvmSemantics.Crypto.Bls12381.G2Point)
    (left right : List (EvmSemantics.Crypto.Bls12381.G2Point × Nat)) :
    foldG2 acc (left ++ right) = foldG2 (foldG2 acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, foldG2]
      exact ih _

end Challenge.Bls12381.ProofSupport.Msm
