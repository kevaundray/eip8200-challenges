set_option warningAsError true

/-! # Parametric source program for Fp2 square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp2.SqrtProgram

structure Result (Pair : Type) where
  exists_ : Bool
  root : Pair

structure Ops (Cell Pair : Type) where
  c0 : Pair → Cell
  c1 : Pair → Cell
  zero : Pair
  pair : Cell → Cell → Pair
  isZeroPair : Pair → Bool
  isZeroCell : Cell → Bool
  eqCell : Cell → Cell → Bool
  eqPair : Pair → Pair → Bool
  add : Cell → Cell → Cell
  sub : Cell → Cell → Cell
  neg : Cell → Cell
  mul : Cell → Cell → Cell
  square : Cell → Cell
  sqrt : Cell → Cell
  inv : Cell → Cell
  squarePair : Pair → Pair
  invTwo : Cell

/-- The one authoritative source program, including every branch and reuse. -/
def run {Cell Pair : Type} (ops : Ops Cell Pair) (a : Pair) : Result Pair :=
  if ops.isZeroPair a then { exists_ := true, root := ops.zero }
  else
    let norm := ops.add (ops.square (ops.c0 a)) (ops.square (ops.c1 a))
    let t := ops.sqrt norm
    if !(ops.eqCell (ops.square t) norm) then
      { exists_ := false, root := ops.zero }
    else
      let alpha := ops.mul (ops.add (ops.c0 a) t) ops.invTwo
      let alphaRoot := ops.sqrt alpha
      let x0 :=
        if !(ops.eqCell (ops.square alphaRoot) alpha) then
          let beta := ops.mul (ops.sub (ops.c0 a) t) ops.invTwo
          ops.sqrt beta
        else alphaRoot
      let x1 :=
        if ops.isZeroCell x0 then
          ops.sqrt (ops.neg (ops.c0 a))
        else
          ops.mul (ops.c1 a) (ops.inv (ops.add x0 x0))
      let root := ops.pair x0 x1
      if !(ops.eqPair (ops.squarePair root) a) then
        { exists_ := false, root := ops.zero }
      else { exists_ := true, root }

theorem run_good {Cell Pair : Type} (ops : Ops Cell Pair)
    (GoodCell : Cell → Prop) (GoodPair : Pair → Prop)
    (hzero : GoodPair ops.zero)
    (hpair : ∀ x y, GoodCell x → GoodCell y → GoodPair (ops.pair x y))
    (hadd : ∀ x y, GoodCell x → GoodCell y → GoodCell (ops.add x y))
    (hsub : ∀ x y, GoodCell x → GoodCell y → GoodCell (ops.sub x y))
    (hneg : ∀ x, GoodCell x → GoodCell (ops.neg x))
    (hmul : ∀ x y, GoodCell x → GoodCell y → GoodCell (ops.mul x y))
    (hsquare : ∀ x, GoodCell x → GoodCell (ops.square x))
    (hsqrt : ∀ x, GoodCell x → GoodCell (ops.sqrt x))
    (hinv : ∀ x, GoodCell x → GoodCell (ops.inv x))
    (hinvTwo : GoodCell ops.invTwo) (a : Pair)
    (ha : GoodCell (ops.c0 a) ∧ GoodCell (ops.c1 a)) :
    GoodPair (run ops a).root := by
  unfold run
  split
  · exact hzero
  · have hnorm := hadd _ _ (hsquare _ ha.1) (hsquare _ ha.2)
    have ht := hsqrt _ hnorm
    dsimp only
    split
    · exact hzero
    · have halpha := hmul _ _ (hadd _ _ ha.1 ht) hinvTwo
      have halphaRoot := hsqrt _ halpha
      split
      · have hbeta := hmul _ _ (hsub _ _ ha.1 ht) hinvTwo
        have hx0 := hsqrt _ hbeta
        split
        · have hx1 := hsqrt _ (hneg _ ha.1)
          split
          · exact hzero
          · exact hpair _ _ hx0 hx1
        · have hx1 := hmul _ _ ha.2 (hinv _ (hadd _ _ hx0 hx0))
          split
          · exact hzero
          · exact hpair _ _ hx0 hx1
      · split
        · have hx1 := hsqrt _ (hneg _ ha.1)
          split
          · exact hzero
          · exact hpair _ _ halphaRoot hx1
        · have hx1 := hmul _ _ ha.2
            (hinv _ (hadd _ _ halphaRoot halphaRoot))
          split
          · exact hzero
          · exact hpair _ _ halphaRoot hx1

theorem run_success {Cell Pair : Type} (ops : Ops Cell Pair) (a : Pair)
    (hzero : ops.isZeroPair a = true → ops.squarePair ops.zero = a)
    (heq : ∀ x y, ops.eqPair x y = true → x = y)
    (hsuccess : (run ops a).exists_ = true) :
    ops.squarePair (run ops a).root = a := by
  generalize hrun : run ops a = result at hsuccess ⊢
  cases result with
  | mk found root =>
      dsimp only at hsuccess
      subst found
      have hfinish (candidate : Pair)
          (h : (if !(ops.eqPair (ops.squarePair candidate) a) then
              ({ exists_ := false, root := ops.zero } : Result Pair)
            else ({ exists_ := true, root := candidate } : Result Pair)) =
              ({ exists_ := true, root := root } : Result Pair)) :
          ops.squarePair root = a := by
        split at h
        · simp at h
        · have hroot := congrArg Result.root h.symm
          dsimp only at hroot
          rw [hroot]
          apply heq
          have hnot : (!(ops.eqPair (ops.squarePair candidate) a)) ≠ true := by
            assumption
          simpa using hnot
      unfold run at hrun
      split at hrun
      · have hroot : root = ops.zero := by simpa using congrArg Result.root hrun.symm
        rw [hroot]
        exact hzero (by assumption)
      · dsimp only at hrun
        split at hrun
        · simp at hrun
        · split at hrun <;> split at hrun <;> exact hfinish _ hrun

end Challenge.Bls12381.ProofSupport.Fp2.SqrtProgram
