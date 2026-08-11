import Challenge.Bls12381.ProofSupport.Fp12

set_option warningAsError true

namespace Checks.Bls12381Fp12

open Challenge.Bls12381.ProofSupport

example : Challenge.Bls12381.ProofSupport.Fp12.toField
    Challenge.Bls12381.ProofSupport.Fp12.zero = 0 :=
  Challenge.Bls12381.ProofSupport.Fp12.toField_zero

example : Challenge.Bls12381.ProofSupport.Fp12.toField
    Challenge.Bls12381.ProofSupport.Fp12.one = 1 :=
  Challenge.Bls12381.ProofSupport.Fp12.toField_one

example (a : Fp12.Repr) :
    Challenge.Bls12381.ProofSupport.Fp12.pow a 0 =
      Challenge.Bls12381.ProofSupport.Fp12.one :=
  Challenge.Bls12381.ProofSupport.Fp12.pow_zero a

example (a : Fp12.Repr) :
    Challenge.Bls12381.ProofSupport.Fp12.toField
        (Challenge.Bls12381.ProofSupport.Fp12.conj a) =
      _root_.Fp12.conj
        (Challenge.Bls12381.ProofSupport.Fp12.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp12.toField_conj a

example (a : Fp12.Repr) (b0 b1 b4 : Fp2.Repr) :
    Challenge.Bls12381.ProofSupport.Fp12.toField
        (Challenge.Bls12381.ProofSupport.Fp12.mulBy014 a b0 b1 b4) =
      _root_.Fp12.mulBy014
        (Challenge.Bls12381.ProofSupport.Fp12.toField a)
        (Challenge.Bls12381.ProofSupport.Fp2.toField b0)
        (Challenge.Bls12381.ProofSupport.Fp2.toField b1)
        (Challenge.Bls12381.ProofSupport.Fp2.toField b4) :=
  Challenge.Bls12381.ProofSupport.Fp12.toField_mulBy014 a b0 b1 b4

example (gammaW gammaV gammaV2 : Fp2.Repr) (a : Fp12.Repr) :
    Challenge.Bls12381.ProofSupport.Fp12.toField
        (Challenge.Bls12381.ProofSupport.Fp12.frobenius gammaW gammaV gammaV2 a) =
      _root_.Fp12.frobenius
        (Challenge.Bls12381.ProofSupport.Fp2.toField gammaW)
        (Challenge.Bls12381.ProofSupport.Fp2.toField gammaV)
        (Challenge.Bls12381.ProofSupport.Fp2.toField gammaV2)
        (Challenge.Bls12381.ProofSupport.Fp12.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp12.toField_frobenius gammaW gammaV gammaV2 a

example (invert : Fp6.Repr → Fp6.Repr) (a : Fp12.Repr)
    (hinvert : Challenge.Bls12381.ProofSupport.Fp6.toField
        (invert (Challenge.Bls12381.ProofSupport.Fp12.invNorm a)) =
      _root_.Fp6.inv (Challenge.Bls12381.ProofSupport.Fp6.toField
        (Challenge.Bls12381.ProofSupport.Fp12.invNorm a))) :
    Challenge.Bls12381.ProofSupport.Fp12.toField
        (Challenge.Bls12381.ProofSupport.Fp12.invWith invert a) =
      _root_.Fp12.inv (Challenge.Bls12381.ProofSupport.Fp12.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp12.toField_invWith invert a hinvert

#print axioms Challenge.Bls12381.ProofSupport.Fp12.toField_conj
#print axioms Challenge.Bls12381.ProofSupport.Fp12.toField_mulBy014
#print axioms Challenge.Bls12381.ProofSupport.Fp12.toField_frobenius
#print axioms Challenge.Bls12381.ProofSupport.Fp12.toField_invWith
#print axioms Challenge.Bls12381.ProofSupport.Fp12.refines_pow

end Checks.Bls12381Fp12
