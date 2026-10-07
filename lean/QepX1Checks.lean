import QepX1JointFinite

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QepX1
noncomputable section
open QepCorrected QepGram QepV3
open scoped BigOperators

def checkX : Mat (Fin 1) (Fin 2) := !![1,0]
def checkZ (b : Bool) : Mat (Fin 1) (Fin 2) := if b then !![2,-1] else !![0,1]
def checkE (b : Bool) : Mat (Fin 1) (Fin 1) := if b then !![1/2] else !![-1/2]
def checkFirstE (b : Bool) : Mat (Fin 1) (Fin 2) := if b then !![1,-1] else !![-1,1]
def checkOutput (a : ℝ) (ω : Bool × Bool) : Mat (Fin 1) (Fin 2) :=
  (correctedWeight (!![1] : Mat (Fin 1) (Fin 1)) checkX (checkZ ω.1) a+checkE ω.2)*checkZ ω.1

theorem check_first_layer_actual (b : Bool) :
    (checkX+checkFirstE b)*(1 : Mat (Fin 2) (Fin 2))=checkZ b := by
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [checkX,checkFirstE,checkZ]

theorem check_gram_inverse_false : (gram (checkZ false))⁻¹=(!![1] : Mat (Fin 1) (Fin 1)) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i
  fin_cases j
  norm_num [gram,checkZ,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,dotProduct,Fin.sum_univ_two,Fin.sum_univ_succ]

theorem check_gram_inverse_true : (gram (checkZ true))⁻¹=(!![1/5] : Mat (Fin 1) (Fin 1)) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i
  fin_cases j
  norm_num [gram,checkZ,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,dotProduct,Fin.sum_univ_two,Fin.sum_univ_succ]

theorem check_input_legal (b : Bool) : IsUnit (gram (checkZ b)).det := by
  cases b <;> norm_num [gram,checkZ,Matrix.det_fin_one,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,dotProduct,Fin.sum_univ_two]

theorem check_missing_teacher_row : checkX*gramProjection (checkZ false) ≠ checkX := by
  intro h
  have h00 := congrArg (fun M : Mat (Fin 1) (Fin 2) => M 0 0) h
  rw [gramProjection,check_gram_inverse_false] at h00
  norm_num [checkX,checkZ,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,dotProduct,Fin.sum_univ_two,Fin.sum_univ_succ] at h00

theorem check_actual_outputs :
    checkOutput 1 (false,false)=!![0,-1/2] ∧
    checkOutput 1 (false,true)=!![0,1/2] ∧
    checkOutput 1 (true,false)=!![-1/5,1/10] ∧
    checkOutput 1 (true,true)=!![9/5,-9/10] := by
  unfold checkOutput correctedWeight correction
  rw [check_gram_inverse_false,check_gram_inverse_true]
  repeat' constructor
  all_goals ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num [checkX,checkZ,checkE,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,dotProduct,Fin.sum_univ_two,Fin.sum_univ_succ]

theorem check_qep_mean : mean (fun _ : Bool × Bool => (1/4 : ℝ)) (checkOutput 1)=!![2/5,-1/5] := by
  obtain ⟨h00,h01,h10,h11⟩ := check_actual_outputs
  ext i j
  fin_cases i
  fin_cases j <;>
    norm_num [mean,Fintype.sum_prod_type,Fintype.sum_bool,h00,h01,h10,h11]

theorem check_qep_not_unbiased : mean (fun _ : Bool × Bool => (1/4 : ℝ)) (checkOutput 1) ≠ checkX := by
  rw [check_qep_mean]
  intro h
  have hh := congrArg (fun M : Mat (Fin 1) (Fin 2) => M 0 0) h
  norm_num [checkX] at hh

theorem check_actual_mse :
    (∑ ω : Bool × Bool,(1/4 : ℝ)*fSq (checkOutput 1 ω-checkX))=27/20 ∧
    (∑ ω : Bool × Bool,(1/4 : ℝ)*fSq (checkOutput 0 ω-checkX))=11/4 := by
  obtain ⟨h00,h01,h10,h11⟩ := check_actual_outputs
  constructor
  · norm_num [Fintype.sum_prod_type,Fintype.sum_bool,h00,h01,h10,h11,fSq,checkX,Fin.sum_univ_succ]
  · norm_num [Fintype.sum_prod_type,Fintype.sum_bool,checkOutput,correctedWeight,checkZ,checkE,
      checkX,fSq,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,dotProduct,Fin.sum_univ_two,Fin.sum_univ_succ]



def checkSampleCov (a : ℝ) : Mat (Fin 2) (Fin 2) :=
  mean (fun _ : Bool × Bool => (1/4 : ℝ)) (fun ω =>
    (checkOutput a ω-checkX).transpose*(checkOutput a ω-checkX))

theorem check_sample_covariances :
    checkSampleCov 1=!![51/50,-21/100;-21/100,33/100] ∧
    checkSampleCov 0=!![3/2,-5/4;-5/4,5/4] := by
  obtain ⟨h00,h01,h10,h11⟩ := check_actual_outputs
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [checkSampleCov,mean,Fintype.sum_prod_type,Fintype.sum_bool,h00,h01,h10,h11,
        checkX,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,dotProduct,Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [checkSampleCov,mean,Fintype.sum_prod_type,Fintype.sum_bool,checkOutput,
        correctedWeight,checkZ,checkE,checkX,Matrix.mul_apply,Matrix.vecMul,Matrix.vecHead,
        dotProduct,Fin.sum_univ_succ]

theorem check_sample_order_false : ¬PSDLe (checkSampleCov 1) (checkSampleCov 0) := by
  intro h
  have hh := h.dotProduct_mulVec_nonneg (![1,1] : Fin 2 → ℝ)
  rw [check_sample_covariances.1,check_sample_covariances.2] at hh
  norm_num [dotProduct,Matrix.mulVec,Fin.sum_univ_two] at hh

end
end QepX1
