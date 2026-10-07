import QepFeedbackFiniteL2
set_option maxHeartbeats 2000000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackMoments QepFeedbackFiniteL2
namespace QepFeedbackConditionalMoments
noncomputable section

theorem integral_of_preserving {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {f : Ω → Ξ} (mp : MeasurePreserving f μ ν)
    (g : Ξ → ℝ) (hg : Integrable g ν) : (∫ x, g (f x) ∂μ)=∫ y, g y ∂ν := by
  have hm : AEStronglyMeasurable g (Measure.map f μ) := by rw [mp.map_eq]; exact hg.aestronglyMeasurable
  have h := integral_map mp.measurable.aemeasurable hm
  rw [mp.map_eq] at h
  exact h.symm


theorem predictable_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (mode : Option ℕ) (t : Ω → ℝ) (ht : Measurable t)
    (o : Ω → ℝ) (ho : MemLp o 2 μ) (delta : ℝ) :
    Integrable (fun p : Ω × ℝ => (o p.1+delta*innovation mode (t p.1) p.2)^2) (μ.prod noise) := by
  have mp := complete_history_law μ mode t ht
  exact mp.integrable_comp_of_integrable
    (add_fresh_square_integrable μ o (MemLp.integrable (by norm_num) ho) ho.integrable_sq delta)

theorem predictable_square_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (mode : Option ℕ) (t : Ω → ℝ) (ht : Measurable t)
    (o : Ω → ℝ) (ho : MemLp o 2 μ) (delta : ℝ) :
    (∫ p : Ω × ℝ, (o p.1+delta*innovation mode (t p.1) p.2)^2 ∂μ.prod noise)=
      (∫ x, (o x)^2 ∂μ)+delta^2/12 := by
  have mp := complete_history_law μ mode t ht
  exact (integral_of_preserving mp (fun p : Ω × ℝ => (o p.1+delta*p.2)^2)
    (add_fresh_square_integrable μ o (MemLp.integrable (by norm_num) ho) ho.integrable_sq delta)).trans
    (add_fresh_second μ o (MemLp.integrable (by norm_num) ho) ho.integrable_sq delta)


theorem predictable_cross_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (mode : Option ℕ) (t : Ω → ℝ) (ht : Measurable t)
    (o : Ω → ℝ) (ho : Integrable o μ) :
    (∫ p : Ω × ℝ, o p.1 * innovation mode (t p.1) p.2 ∂μ.prod noise)=0 := by
  have mp := complete_history_law μ mode t ht
  calc
    _ = ∫ p : Ω × ℝ, o p.1*p.2 ∂μ.prod noise :=
      integral_of_preserving mp _ (ho.mul_prod id_integrable)
    _ = 0 := by rw [integral_prod_mul o (fun u : ℝ => u),noise_mean,mul_zero]

end
end QepFeedbackConditionalMoments
