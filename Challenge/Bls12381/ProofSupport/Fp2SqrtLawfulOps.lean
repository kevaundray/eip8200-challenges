import Challenge.Bls12381.ProofSupport.Fp2SqrtProgram
import Challenge.Bls12381.ProofSupport.Fp2SqrtConstants
import Challenge.Bls12381.ProofSupport.LawfulFp2

set_option warningAsError true

/-! # Lawful interpretation of the Fp2 square-root program -/

namespace Challenge.Bls12381.ProofSupport.Fp2

open PrimeField

irreducible_def lawfulSqrt (lemma := lawfulSqrt_eq)
    (x : LawfulFp2.Base) : LawfulFp2.Base :=
  x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4)

def lawfulInvTwo : LawfulFp2.Base :=
  (Fp.value invTwo : LawfulFp2.Base)

def lawfulSqrtOps : SqrtProgram.Ops LawfulFp2.Base LawfulFp2.Carrier where
  c0 := QuadraticAlgebra.re
  c1 := QuadraticAlgebra.im
  zero := 0
  pair := fun c0 c1 => ⟨c0, c1⟩
  isZeroPair := fun a => decide (a = 0)
  isZeroCell := fun a => decide (a = 0)
  eqCell := fun a b => decide (a = b)
  eqPair := fun a b => decide (a = b)
  add := fun a b => a + b
  sub := fun a b => a - b
  neg := (- .)
  mul := fun a b => a * b
  square := fun a => a ^ 2
  sqrt := lawfulSqrt
  inv := Inv.inv
  squarePair := fun a => a * a
  invTwo := lawfulInvTwo

end Challenge.Bls12381.ProofSupport.Fp2
