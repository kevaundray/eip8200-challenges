import Challenge.Bls12381.ProofSupport.Fp2

set_option warningAsError true

/-! # Canonical decoded representation of an Fp2 element -/

namespace Challenge.Bls12381.ProofSupport.Fp2

/-- Both decoded 48-byte components are canonical BLS base-field values. -/
def Canonical (a : Repr) : Prop := Fp.Canonical a.c0 ∧ Fp.Canonical a.c1

end Challenge.Bls12381.ProofSupport.Fp2
