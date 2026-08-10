import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

namespace Checks.Bls12381ScalarMul

open Challenge.Bls12381.ProofSupport

example (point : G1Projective.Point) :
    ScalarMul.g1 0 point = G1Projective.infinity := ScalarMul.g1_zero point
example (point : G1Projective.Point) : ScalarMul.g1 1 point = point :=
  ScalarMul.g1_one point
example (point : G2Projective.Point) :
    ScalarMul.g2 0 point = G2Projective.infinity := ScalarMul.g2_zero point
example (point : G2Projective.Point) : ScalarMul.g2 1 point = point :=
  ScalarMul.g2_one point

#print axioms ScalarMul.g1_one
#print axioms ScalarMul.g2_one
#print axioms ScalarMul.loopG1_step

end Checks.Bls12381ScalarMul
