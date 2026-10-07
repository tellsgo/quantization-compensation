import QepReluLegality
set_option maxHeartbeats 1000000
open MeasureTheory Set
open QepFiniteDitherLaw QepReluIntegrals QepReluProcess QepReluExpectation
namespace QepReluProbability
noncomputable section

def positive (x : ℝ) : ℝ := if 0<x then 1 else 0

theorem positive_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω→ℝ} (hf : Measurable f) :
    Integrable (fun x => positive (f x)) μ := by
  change Integrable ({x | 0<f x}.indicator (fun _ => (1:ℝ))) μ
  exact (integrable_const (1:ℝ)).indicator (measurableSet_lt measurable_const hf)

theorem positive_integral_measure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω→ℝ} (hf : Measurable f) :
    (∫ x, positive (f x) ∂μ)=μ.real {x | 0<f x} := by
  exact integral_indicator_one (measurableSet_lt measurable_const hf)

theorem uniform_tail (c : ℝ) (hc : -(1/2:ℝ)≤c) (hc' : c≤1/2) :
    (∫ v, (if c<v then (1:ℝ) else 0) ∂noise)=1/2-c := by
  change (∫ v, (Ioi c).indicator (fun _ => (1:ℝ)) v ∂noise)=_
  rw [integral_indicator_const (1:ℝ) (s:=Ioi c) measurableSet_Ioi]
  simp only [smul_eq_mul,mul_one]
  change (noise (Ioi c)).toReal=_
  rw [noise, Measure.restrict_apply measurableSet_Ioi]
  have hset : Ioi c ∩ Ioc (-(1/2:ℝ)) (1/2)=Ioc c (1/2) := by
    ext v
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    constructor
    · rintro ⟨h,_,h'⟩; exact ⟨h,h'⟩
    · rintro ⟨h,h'⟩; exact ⟨h,lt_of_le_of_lt hc h,h'⟩
  rw [hset,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hc')]

theorem qep_positive_inner (z : ℝ) (hz : (1/2:ℝ)≤z) :
    (∫ v, positive (relu (v*z-1/4)) ∂noise)=1/2-1/(4*z) := by
  have hp : 0<z := by linarith
  have heq (v : ℝ) : (0<relu (v*z-1/4)) ↔ 1/(4*z)<v := by
    simp only [relu,lt_max_iff,lt_self_iff_false,false_or]
    rw [div_lt_iff₀ (show 0<4*z by positivity)]
    constructor <;> intro h <;> nlinarith
  simp_rw [positive,heq]
  apply uniform_tail
  · exact le_trans (by norm_num : -(1/2:ℝ)≤0) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0<4*z)).2
    linarith

theorem base_positive_inner (z : ℝ) (hz : 0<z) :
    (∫ v, positive (relu ((v-1/4)*z)) ∂noise)=(1/4:ℝ) := by
  have heq (v : ℝ) : (0<relu ((v-1/4)*z)) ↔ (1/4:ℝ)<v := by
    simp only [relu,lt_max_iff,lt_self_iff_false,false_or,mul_pos_iff_of_pos_right hz,sub_pos]
  simp_rw [positive,heq]
  convert uniform_tail (1/4) (by norm_num) (by norm_num) using 1
  norm_num

theorem qep_positive_outer :
    (∫ z in (1/2:ℝ)..(3/2), 1/2-1/(4*z))=1/2-Real.log 3/4 := by
  have hc : ContinuousOn (fun z : ℝ => 1/z) (Icc (1/2) (3/2)) := by
    apply continuousOn_const.div continuousOn_id
    intro z hz; change z≠0; linarith [hz.1]
  have hi : IntervalIntegrable (fun z : ℝ => 1/z) volume (1/2) (3/2) := hc.intervalIntegrable_of_Icc (by norm_num)
  have heq (z : ℝ) : 1/(4*z)=(1/z)/4 := by ring
  simp_rw [heq]
  rw [intervalIntegral.integral_sub (f:=fun _ : ℝ => 1/2)
    (continuous_const.intervalIntegrable _ _) (hi.div_const 4),
    intervalIntegral.integral_div (4:ℝ) (fun z : ℝ => 1/z),
    integral_one_div_of_pos (by norm_num) (by norm_num), intervalIntegral.integral_const]
  norm_num

theorem base_positive_probability :
    (∫ e, positive (baseOutput e) ∂noise.prod noise)=(1/4:ℝ) := by
  have hm : Measurable baseOutput := by unfold baseOutput relu; fun_prop
  rw [integral_prod _ (positive_integrable _ hm), noise_integral]
  calc
    _ = ∫ u in (-(1/2:ℝ))..(1/2), (1/4:ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu; dsimp only
      rw [uIcc_of_le (by norm_num)] at hu
      exact base_positive_inner (1+u) (by linarith [hu.1])
    _ = 1/4 := by rw [intervalIntegral.integral_const]; norm_num

theorem qep_positive_probability :
    (∫ e, positive (qepOutput e) ∂noise.prod noise)=(1/2-Real.log 3/4:ℝ) := by
  have hm : Measurable qepOutput := by unfold qepOutput relu; fun_prop
  rw [integral_prod _ (positive_integrable _ hm), noise_integral]
  have heq : (∫ u in (-(1/2:ℝ))..(1/2), ∫ v, positive (qepOutput (u,v)) ∂noise)=
      ∫ u in (-(1/2:ℝ))..(1/2), 1/2-1/(4*(u+1)) := by
    apply intervalIntegral.integral_congr
    intro u hu; dsimp only
    rw [uIcc_of_le (by norm_num)] at hu
    change (∫ v, positive (relu (v*(1+u)-1/4)) ∂noise)=_
    rw [add_comm 1 u]
    exact qep_positive_inner (u+1) (by linarith [hu.1])
  rw [heq,intervalIntegral.integral_comp_add_right (fun z : ℝ => 1/2-1/(4*z)) 1]
  norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num, show (1/2:ℝ)+1=3/2 by norm_num]
  exact qep_positive_outer

theorem actual_positive_probability_base :
    (noise.prod noise).real {d | 0<actualBase d}=(1/4:ℝ) := by
  have hm : Measurable actualBase := by
    have heq : actualBase = fun d => baseOutput (errors false d) := funext actual_base_identity
    rw [heq]
    exact (show Measurable baseOutput by unfold baseOutput relu; fun_prop).comp (actual_innovation_law false).measurable
  rw [←positive_integral_measure _ hm]
  simp_rw [actual_base_identity]
  rw [integral_of_preserving (actual_innovation_law false) (fun e => positive (baseOutput e))
    (positive_integrable _ (by unfold baseOutput relu; fun_prop))]
  exact base_positive_probability

theorem actual_positive_probability_qep :
    (noise.prod noise).real {d | 0<actualQep d}=(1/2-Real.log 3/4:ℝ) := by
  have ht : Measurable (fun d : ℝ×ℝ => target d.1) := target_measurable.comp measurable_fst
  have hf : Measurable (fun d : ℝ×ℝ => first d.1) := by
    have heq : (fun d : ℝ×ℝ => first d.1)=fun d => 1+firstError d.1 := by funext d; exact first_eq d.1
    rw [heq]; exact measurable_const.add (first_error_measurable.comp measurable_fst)
  have hm : Measurable actualQep := by
    unfold actualQep qqep quantize relu
    exact measurable_const.max (((grid_measurable.comp (ht.add measurable_snd)).sub measurable_snd).mul hf)
  rw [←positive_integral_measure _ hm]
  simp_rw [actual_qep_identity]
  rw [integral_of_preserving (actual_innovation_law true) (fun e => positive (qepOutput e))
    (positive_integrable _ (by unfold qepOutput relu; fun_prop))]
  exact qep_positive_probability

theorem actual_less_often_positive :
    (noise.prod noise).real {d | 0<actualQep d} < (noise.prod noise).real {d | 0<actualBase d} := by
  rw [actual_positive_probability_base,actual_positive_probability_qep]
  linarith [log_three_gt]

end
end QepReluProbability
