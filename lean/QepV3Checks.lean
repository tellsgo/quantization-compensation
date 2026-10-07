import QepV3Order

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QepV3
noncomputable section
open QepCorrected QepGram

def witnessTeacher : Mat (Fin 1) (Fin 2) := !![1,0]
def witnessStudent : Mat (Fin 1) (Fin 2) := !![0,1]

theorem witness_gram_legal : gram witnessStudent=1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [gram,witnessStudent,Matrix.mul_apply,Fin.sum_univ_two]

theorem witness_missing_row : witnessTeacher*gramProjection witnessStudent ≠ witnessTeacher := by
  intro h
  have he := congrArg (fun M : Mat (Fin 1) (Fin 2) => M 0 0) h
  norm_num [gramProjection,witness_gram_legal,witnessTeacher,witnessStudent,
    Matrix.mul_apply,Fin.sum_univ_two,Fin.sum_univ_succ] at he




theorem witness_actual_residual :
    fSq ((correctedWeight (!![1] : Mat (Fin 1) (Fin 1)) witnessTeacher witnessStudent 1)*
      witnessStudent-(!![1] : Mat (Fin 1) (Fin 1))*witnessTeacher)=1 := by
  unfold correctedWeight correction
  rw [witness_gram_legal]
  norm_num [witnessTeacher,witnessStudent,Matrix.mul_apply,Fin.sum_univ_two,Fin.sum_univ_succ,fSq]
  norm_num [Matrix.vecHead,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]


theorem witness_marginal_zero : (1/2 : ℝ)*(1/2)+(1/2)*(-1/2)=0 := by norm_num

theorem witness_past_cross_nonzero : (1/2 : ℝ)*((1/2)*(1/2))+(1/2)*((-1/2)*(-1/2))=1/4 := by norm_num


theorem witness_different_operator : (1:ℝ)^2 < (2:ℝ)^2 := by norm_num

end
end QepV3
