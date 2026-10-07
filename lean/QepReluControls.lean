import QepReluProbability
set_option maxHeartbeats 1000000
open MeasureTheory Set
open QepFiniteDitherLaw QepReluIntegrals QepReluProcess QepReluExpectation QepReluLegality QepReluProbability
namespace QepReluControls
noncomputable section

theorem loss_order_reversal_false : ¬ ((∫ d, (actualQep d)^2 ∂noise.prod noise) ≤
    ∫ d, (actualBase d)^2 ∂noise.prod noise) := by
  linarith [actual_strict_gap]

theorem positivity_order_reversal_false : ¬ ((noise.prod noise).real {d | 0<actualBase d} ≤
    (noise.prod noise).real {d | 0<actualQep d}) := not_le_of_gt actual_less_often_positive

theorem base_weight_zero_at_origin : qbase (0,0)=0 := by
  have hr : round (-(1/4:ℝ))=0 := round_eq_zero_iff.mpr (by norm_num)
  change ((round (-(1/4:ℝ)+0) : ℤ) : ℝ)-0=0
  rw [add_zero,hr]
  norm_num

theorem pointwise_weight_invertibility_false : ¬ (∀ d : ℝ×ℝ, qbase d ≠ 0) := by
  intro h
  exact h (0,0) base_weight_zero_at_origin

theorem physical_seed_error_mismatch :
    (errors false (1/4,-1/5)).2 ≠ (errors true (1/4,-1/5)).2 := by
  have hfirst : round (1+(1/4:ℝ))=1 := round_eq_iff.mpr (by norm_num)
  have hb : round (-(1/4:ℝ)+(-1/5))=0 := round_eq_zero_iff.mpr (by norm_num)
  have hq : round (-(1/3:ℝ)+(-1/5))= -1 := round_eq_iff.mpr (by norm_num)
  have hf : first (1/4)=(3/4:ℝ) := by norm_num [first,quantize,grid,relu,hfirst]
  have ht : target (1/4)=-(1/3:ℝ) := by rw [target_eq,hf]; norm_num
  norm_num [errors,quantize,grid,ht,hb,hq]

theorem base_second_moment_integrable : Integrable (fun d => (actualBase d)^2) (noise.prod noise) := by
  have heq : (fun d => (actualBase d)^2)=fun d => (baseOutput (errors false d))^2 := by
    funext d; rw [actual_base_identity]
  rw [heq]
  have hg : Integrable (fun e : ℝ×ℝ => (baseOutput e)^2) (noise.prod noise) :=
    pair_integrable (by unfold baseOutput relu; fun_prop)
  exact (actual_innovation_law false).integrable_comp_of_integrable hg

theorem qep_second_moment_integrable : Integrable (fun d => (actualQep d)^2) (noise.prod noise) := by
  have heq : (fun d => (actualQep d)^2)=fun d => (qepOutput (errors true d))^2 := by
    funext d; rw [actual_qep_identity]
  rw [heq]
  have hg : Integrable (fun e : ℝ×ℝ => (qepOutput e)^2) (noise.prod noise) :=
    pair_integrable (by unfold qepOutput relu; fun_prop)
  exact (actual_innovation_law true).integrable_comp_of_integrable hg

theorem actual_continuous_relu_counterexample :
    Integrable (fun d => (actualBase d)^2) (noise.prod noise) ∧
    Integrable (fun d => (actualQep d)^2) (noise.prod noise) ∧
    (∀ᵐ d : ℝ×ℝ ∂noise.prod noise,
      0 < first d.1*first d.1 ∧ qbase d ≠ 0 ∧ qqep d ≠ 0) ∧
    (1/768:ℝ) < (∫ d, (actualQep d-teacherOutput)^2 ∂noise.prod noise)-
      (∫ d, (actualBase d-teacherOutput)^2 ∂noise.prod noise) ∧
    (noise.prod noise).real {d | 0<actualQep d} < (noise.prod noise).real {d | 0<actualBase d} := by
  refine ⟨base_second_moment_integrable,qep_second_moment_integrable,?_,
    actual_teacher_loss_gap,actual_less_often_positive⟩
  filter_upwards [actual_second_weights_nonzero_ae] with d hd
  exact ⟨input_gram_positive d.1,hd⟩

end
end QepReluControls
