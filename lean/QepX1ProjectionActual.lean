import QepX1OrderBridge
import QepLinearIdentities

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace QepX1
noncomputable section
open QepCorrected QepGram QepV3
variable {n t : Type*} [Fintype n] [Fintype t] [DecidableEq n] [DecidableEq t]



theorem actual_gram_error_identity (X Z : Mat n t) (a : ℝ)
    (hZ : IsUnit (gram Z).det) :
    (Z-X)*(Z-X).transpose-
      (correctedInput X Z a-X)*(correctedInput X Z a-X).transpose=
        (a*(2-a)) • ((Z-X)*gramProjection Z*(Z-X).transpose) :=
  QepLinear.T2_first_identity a Z X (gramProjection Z) (gramProjection_symmetric Z)
    (gramProjection_idempotent Z hZ) (input_times_projection Z hZ)

theorem actual_gram_output_identity (X Z : Mat n t) (a : ℝ)
    (hZ : IsUnit (gram Z).det) :
    (1-a) • (Z*Z.transpose)+a • (X*X.transpose)-
      correctedInput X Z a*(correctedInput X Z a).transpose=
        a • (X*(1-gramProjection Z)*X.transpose)+
          (a*(1-a)) • ((Z-X*gramProjection Z)*(Z-X*gramProjection Z).transpose) :=
  QepLinear.T3_second_identity a Z X (gramProjection Z) (gramProjection_symmetric Z)
    (gramProjection_idempotent Z hZ) (input_times_projection Z hZ)

theorem actual_gram_error_bound (X Z : Mat n t) (a : ℝ)
    (hZ : IsUnit (gram Z).det) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    PSDLe ((correctedInput X Z a-X)*(correctedInput X Z a-X).transpose)
      ((Z-X)*(Z-X).transpose) :=
  QepLinear.T4_first_loewner a Z X (gramProjection Z) (gramProjection_symmetric Z)
    (gramProjection_idempotent Z hZ) (input_times_projection Z hZ) ha (by linarith)

theorem actual_gram_output_bound (X Z : Mat n t) (a : ℝ)
    (hZ : IsUnit (gram Z).det) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    PSDLe (correctedInput X Z a*(correctedInput X Z a).transpose)
      ((1-a) • (Z*Z.transpose)+a • (X*X.transpose)) :=
  QepLinear.T4_second_loewner a Z X (gramProjection Z) (gramProjection_symmetric Z)
    (gramProjection_idempotent Z hZ) (input_times_projection Z hZ) ha ha1

end
end QepX1
