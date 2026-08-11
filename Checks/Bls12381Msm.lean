import Challenge.Bls12381.ProofSupport.Msm

set_option warningAsError true

namespace Checks.Bls12381Msm

open Challenge.Bls12381.ProofSupport

example (acc : G1Affine.Point)
    (left right : List (G1Affine.Point × Nat)) :
    Msm.foldG1 acc (left ++ right) = Msm.foldG1 (Msm.foldG1 acc left) right :=
  Msm.foldG1_append acc left right

example (acc : G2Affine.Point)
    (left right : List (G2Affine.Point × Nat)) :
    Msm.foldG2 acc (left ++ right) = Msm.foldG2 (Msm.foldG2 acc left) right :=
  Msm.foldG2_append acc left right

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG1_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG1_nil

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG1_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG1_cons

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG1_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG1_append

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG2_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG2_nil

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG2_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG2_cons

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG2_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG2_append

end Checks.Bls12381Msm
