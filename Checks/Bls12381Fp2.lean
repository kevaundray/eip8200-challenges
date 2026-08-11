import Challenge.Bls12381.ProofSupport.Fp2

set_option warningAsError true

namespace Checks.Bls12381Fp2

example : Challenge.Bls12381.ProofSupport.Fp2.toField
    Challenge.Bls12381.ProofSupport.Fp2.zero = 0 :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_zero

example : Challenge.Bls12381.ProofSupport.Fp2.toField
    Challenge.Bls12381.ProofSupport.Fp2.one = 1 :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_one

example (a : Challenge.Bls12381.ProofSupport.Fp2.Repr) :
    Challenge.Bls12381.ProofSupport.Fp2.toField
        (Challenge.Bls12381.ProofSupport.Fp2.conj a) =
      _root_.Fp2.conj (Challenge.Bls12381.ProofSupport.Fp2.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_conj a

example
    (invert : Challenge.Bls12381.ProofSupport.Fp.Limbs →
      Challenge.Bls12381.ProofSupport.Fp.Limbs)
    (a : Challenge.Bls12381.ProofSupport.Fp2.Repr)
    (hinvert : Challenge.Bls12381.ProofSupport.Fp.toField
        (invert (Challenge.Bls12381.ProofSupport.Fp2.norm a)) =
      (Challenge.Bls12381.ProofSupport.Fp.toField
        (Challenge.Bls12381.ProofSupport.Fp2.norm a))⁻¹) :
    Challenge.Bls12381.ProofSupport.Fp2.toField
        (Challenge.Bls12381.ProofSupport.Fp2.invWith invert a) =
      _root_.Fp2.inv (Challenge.Bls12381.ProofSupport.Fp2.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_invWith invert a hinvert

#print axioms Challenge.Bls12381.ProofSupport.Fp2.toField_conj
#print axioms Challenge.Bls12381.ProofSupport.Fp2.toField_invWith

end Checks.Bls12381Fp2
