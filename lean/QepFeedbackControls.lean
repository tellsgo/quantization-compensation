import QepFeedbackAdaptive
import QepFeedbackMatrix
set_option maxHeartbeats 1000000
open MeasureTheory Matrix
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra
open QepFeedbackAdaptive QepFeedbackMatrix
namespace QepFeedbackControls
noncomputable section

theorem adaptive_actual_mean_nonzero (w₁ w₂ : ℝ) :
    (∫ u,e₂ w₁ w₂ u ∂noise.prod noise) ≠ 0 := by
  rw [actual_adaptive_second_error_mean]; norm_num

def tWitness : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;0,1]
def dWitness : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,2]

theorem gram_factor_order_matters : tWitness*dWitness*tWitness.transpose ≠
    tWitness.transpose*dWitness*tWitness := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [tWitness,dWitness,Matrix.mul_apply,Fin.sum_univ_two] at h00


theorem zero_step_actual_first_error (p : History 1) :
    errors (fun _ => none) (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ _ => 0) 1 p 0 = -1 := by
  norm_num [errors,Fin.snoc,Fin.lastCases]

end
end QepFeedbackControls
