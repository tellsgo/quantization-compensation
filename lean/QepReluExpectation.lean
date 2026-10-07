import QepReluProcess
set_option maxHeartbeats 1000000
open MeasureTheory Set
open QepFiniteDitherLaw QepReluIntegrals QepReluProcess
namespace QepReluExpectation
noncomputable section

theorem noise_integral (f : ℝ→ℝ) :
    (∫ u, f u ∂noise)=∫ u in (-(1/2:ℝ))..(1/2), f u := by
  exact (intervalIntegral.integral_of_le (by norm_num)).symm

theorem pair_integrable {f : ℝ×ℝ→ℝ} (hf : Continuous f) : Integrable f (noise.prod noise) := by
  unfold noise
  rw [Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem relu_mul_nonneg (z x : ℝ) (hz : 0≤z) : relu (x*z)=z*relu x := by
  by_cases hx : 0≤x
  · simp only [relu, max_eq_right hx, max_eq_right (mul_nonneg hx hz)]
    ring
  · have hx' : x≤0 := le_of_not_ge hx
    simp [relu, max_eq_left hx', max_eq_left (mul_nonpos_of_nonpos_of_nonneg hx' hz)]

theorem base_inner_scaled (z : ℝ) (hz : 0≤z) :
    (∫ v in (-(1/2:ℝ))..(1/2), relu ((v-1/4)*z)^2)=z^2/192 := by
  simp_rw [relu_mul_nonneg z _ hz, mul_pow]
  rw [intervalIntegral.integral_const_mul, base_inner]
  ring

theorem base_innovation_expectation :
    (∫ e, (baseOutput e)^2 ∂noise.prod noise)=(13/2304:ℝ) := by
  have hc : Continuous (fun e : ℝ×ℝ => (baseOutput e)^2) := by unfold baseOutput relu; fun_prop
  rw [integral_prod _ (pair_integrable hc), noise_integral]
  have heq : (∫ u in (-(1/2:ℝ))..(1/2), ∫ v, (baseOutput (u,v))^2 ∂noise)=
      ∫ u in (-(1/2:ℝ))..(1/2), (1+u)^2/192 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    dsimp only
    rw [noise_integral]
    exact base_inner_scaled (1+u) (by linarith [hu.1])
  rw [heq]
  have heq' : (fun u : ℝ => (1+u)^2/192) = fun u => (u+1)^2/192 := by funext u; ring
  rw [heq', intervalIntegral.integral_comp_add_right (fun z : ℝ => z^2/192) 1]
  norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num, show (1/2:ℝ)+1=3/2 by norm_num]
  exact base_outer

theorem qep_innovation_expectation :
    (∫ e, (qepOutput e)^2 ∂noise.prod noise)=(1/72-Real.log 3/192:ℝ) := by
  have hc : Continuous (fun e : ℝ×ℝ => (qepOutput e)^2) := by unfold qepOutput relu; fun_prop
  rw [integral_prod _ (pair_integrable hc), noise_integral]
  have heq : (∫ u in (-(1/2:ℝ))..(1/2), ∫ v, (qepOutput (u,v))^2 ∂noise)=
      ∫ u in (-(1/2:ℝ))..(1/2), (1+u)^2/24-(1+u)/16+1/32-1/(192*(1+u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    dsimp only
    rw [noise_integral]
    exact qep_inner (1+u) (by linarith [hu.1])
  rw [heq]
  have heq' : (fun u : ℝ => (1+u)^2/24-(1+u)/16+1/32-1/(192*(1+u))) =
      fun u => (u+1)^2/24-(u+1)/16+1/32-1/(192*(u+1)) := by funext u; rw [add_comm 1 u]
  rw [heq', intervalIntegral.integral_comp_add_right
    (fun z : ℝ => z^2/24-z/16+1/32-1/(192*z)) 1]
  norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num, show (1/2:ℝ)+1=3/2 by norm_num]
  exact qep_outer

theorem integral_of_preserving {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {f : Ω→Ξ} (mp : MeasurePreserving f μ ν)
    (g : Ξ→ℝ) (hg : Integrable g ν) : (∫ x, g (f x) ∂μ)=∫ y, g y ∂ν := by
  have hm : AEStronglyMeasurable g (Measure.map f μ) := by rw [mp.map_eq]; exact hg.aestronglyMeasurable
  have h := integral_map mp.measurable.aemeasurable hm
  rw [mp.map_eq] at h
  exact h.symm

theorem actual_base_loss : (∫ d, (actualBase d)^2 ∂noise.prod noise)=(13/2304:ℝ) := by
  simp_rw [actual_base_identity]
  rw [integral_of_preserving (actual_innovation_law false) (fun e => (baseOutput e)^2)
    (pair_integrable (by unfold baseOutput relu; fun_prop))]
  exact base_innovation_expectation

theorem actual_qep_loss : (∫ d, (actualQep d)^2 ∂noise.prod noise)=(1/72-Real.log 3/192:ℝ) := by
  simp_rw [actual_qep_identity]
  rw [integral_of_preserving (actual_innovation_law true) (fun e => (qepOutput e)^2)
    (pair_integrable (by unfold qepOutput relu; fun_prop))]
  exact qep_innovation_expectation

theorem actual_strict_gap : (1/768:ℝ) <
    (∫ d, (actualQep d)^2 ∂noise.prod noise)-(∫ d, (actualBase d)^2 ∂noise.prod noise) := by
  rw [actual_base_loss, actual_qep_loss]
  exact strict_gap

end
end QepReluExpectation
