import QepFiniteDitherHistory
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
open MeasureTheory ProbabilityTheory
open QepFiniteDitherLaw QepFiniteDitherHistory
namespace QepContinuousCoordinates
noncomputable section
variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable
def law : Measure (ι → ℝ) := Measure.pi (fun _ : ι => noise)
instance : IsProbabilityMeasure (law (ι:=ι)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : ι => noise)))

theorem eval_law (i : ι) : Measure.map (fun u : ι → ℝ => u i) law = noise :=
  (measurePreserving_eval (fun _ : ι => noise) i).map_eq

theorem eval_power_integrable (i : ι) (n : ℕ) :
    Integrable (fun u : ι → ℝ => (u i)^n) law := by
  have h : Integrable (fun x : ℝ => x^n) (Measure.map (fun u : ι → ℝ => u i) law) := by
    rw [eval_law]; exact noise_integrable_power n
  exact (integrable_map_measure (continuous_id.pow n).aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).mp h

theorem eval_integrable (i : ι) : Integrable (fun u : ι → ℝ => u i) law := by
  simpa using eval_power_integrable i 1

theorem eval_integral (i : ι) (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ u : ι → ℝ, g (u i) ∂law)=∫ x, g x ∂noise := by
  have h := integral_map_of_stronglyMeasurable (measurable_pi_apply i) hg (μ:=law)
  rw [eval_law] at h
  exact h.symm

theorem eval_mean (i : ι) : (∫ u : ι → ℝ, u i ∂law)=0 := by
  exact (eval_integral i id (by fun_prop)).trans noise_mean

theorem eval_second (i : ι) : (∫ u : ι → ℝ, (u i)^2 ∂law)=1/12 := by
  exact (eval_integral i (fun x=>x^2) (by fun_prop)).trans noise_second_moment

theorem coordinates_independent : iIndepFun (fun i (u : ι → ℝ) => u i) law :=
  iIndepFun_pi (X:=fun _ : ι => id) (fun _ => aemeasurable_id)

theorem pair_integrable (i j : ι) : Integrable (fun u : ι → ℝ => u i*u j) law := by
  by_cases h : i=j
  · subst j; simpa [pow_two] using eval_power_integrable i 2
  · exact (coordinates_independent.indepFun h).integrable_mul (eval_integrable i) (eval_integrable j)

theorem pair_expectation (i j : ι) :
    (∫ u : ι → ℝ, u i*u j ∂law) = if i=j then (1/12:ℝ) else 0 := by
  classical
  by_cases h : i=j
  · subst j; simpa [pow_two] using eval_second i
  · rw [ite_eq_right h,(coordinates_independent.indepFun h).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable,
      eval_mean,eval_mean]
    ring
end
end QepContinuousCoordinates
