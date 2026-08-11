import Challenge.Bls12381.ProofSupport.Fp6

set_option warningAsError true

namespace Checks.Bls12381Fp6

open Challenge.Bls12381.ProofSupport

example : Challenge.Bls12381.ProofSupport.Fp6.toField
    Challenge.Bls12381.ProofSupport.Fp6.zero = 0 :=
  Challenge.Bls12381.ProofSupport.Fp6.toField_zero

example : Challenge.Bls12381.ProofSupport.Fp6.toField
    Challenge.Bls12381.ProofSupport.Fp6.one = 1 :=
  Challenge.Bls12381.ProofSupport.Fp6.toField_one

example (a : Fp6.Repr) :
    Challenge.Bls12381.ProofSupport.Fp6.toField
        (Challenge.Bls12381.ProofSupport.Fp6.neg a) =
      -Challenge.Bls12381.ProofSupport.Fp6.toField a :=
  Challenge.Bls12381.ProofSupport.Fp6.toField_neg a

example (a : Fp6.Repr) (b0 b1 : Fp2.Repr) :
    Challenge.Bls12381.ProofSupport.Fp6.toField
        (Challenge.Bls12381.ProofSupport.Fp6.mulBy01 a b0 b1) =
      _root_.Fp6.mulBy01
        (Challenge.Bls12381.ProofSupport.Fp6.toField a)
        (Challenge.Bls12381.ProofSupport.Fp2.toField b0)
        (Challenge.Bls12381.ProofSupport.Fp2.toField b1) :=
  Challenge.Bls12381.ProofSupport.Fp6.toField_mulBy01 a b0 b1

example (gammaV gammaV2 : Fp2.Repr) (a : Fp6.Repr) :
    Challenge.Bls12381.ProofSupport.Fp6.toField
        (Challenge.Bls12381.ProofSupport.Fp6.frobenius gammaV gammaV2 a) =
      { c0 := _root_.Fp2.conj
          (Challenge.Bls12381.ProofSupport.Fp2.toField a.c0)
        c1 := Challenge.Bls12381.ProofSupport.Fp2.toField gammaV *
          _root_.Fp2.conj (Challenge.Bls12381.ProofSupport.Fp2.toField a.c1)
        c2 := Challenge.Bls12381.ProofSupport.Fp2.toField gammaV2 *
          _root_.Fp2.conj (Challenge.Bls12381.ProofSupport.Fp2.toField a.c2) } :=
  Challenge.Bls12381.ProofSupport.Fp6.toField_frobenius gammaV gammaV2 a

example (invert : Fp2.Repr → Fp2.Repr) (a : Fp6.Repr)
    (hinvert : Challenge.Bls12381.ProofSupport.Fp2.toField
        (invert (Challenge.Bls12381.ProofSupport.Fp6.invNorm a)) =
      _root_.Fp2.inv (Challenge.Bls12381.ProofSupport.Fp2.toField
        (Challenge.Bls12381.ProofSupport.Fp6.invNorm a))) :
    Challenge.Bls12381.ProofSupport.Fp6.toField
        (Challenge.Bls12381.ProofSupport.Fp6.invWith invert a) =
      _root_.Fp6.inv (Challenge.Bls12381.ProofSupport.Fp6.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp6.toField_invWith invert a hinvert

#print axioms Challenge.Bls12381.ProofSupport.Fp6.toField_mulBy01
#print axioms Challenge.Bls12381.ProofSupport.Fp6.toField_frobenius
#print axioms Challenge.Bls12381.ProofSupport.Fp6.toField_invWith

end Checks.Bls12381Fp6
