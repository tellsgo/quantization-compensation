import QepContinuousCoordinates
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
open MeasureTheory
namespace QepFiniteMomentAssembly
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

def linear (ξ : ι → Ω → ℝ) (b : ι → ℝ) (ω : Ω) := ∑ i, b i*ξ i ω

theorem linear_integrable (ξ : ι → Ω → ℝ) (b : ι → ℝ)
    (hi : ∀ i, Integrable (ξ i) μ) : Integrable (linear ξ b) μ := by
  exact integrable_finsetSum Finset.univ (fun i _ => (hi i).const_mul (b i))

theorem linear_mean (ξ : ι → Ω → ℝ) (b : ι → ℝ)
    (hi : ∀ i, Integrable (ξ i) μ) (hm : ∀ i, (∫ ω, ξ i ω ∂μ)=0) :
    (∫ ω, linear ξ b ω ∂μ)=0 := by
  unfold linear
  rw [integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (b i))]
  simp [integral_const_mul,hm]

theorem linear_square_expand (ξ : ι → Ω → ℝ) (b : ι → ℝ) (ω : Ω) :
    (linear ξ b ω)^2=∑ i, ∑ j, (b i*b j)*(ξ i ω*ξ j ω) := by
  unfold linear
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

theorem linear_square_integrable (ξ : ι → Ω → ℝ) (b : ι → ℝ)
    (hij : ∀ i j, Integrable (fun ω => ξ i ω*ξ j ω) μ) :
    Integrable (fun ω => (linear ξ b ω)^2) μ := by
  simp_rw [linear_square_expand]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hij i j).const_mul (b i*b j)))

theorem linear_second (ξ : ι → Ω → ℝ) (b variance : ι → ℝ)
    (hij : ∀ i j, Integrable (fun ω => ξ i ω*ξ j ω) μ)
    (hc : ∀ i j, (∫ ω, ξ i ω*ξ j ω ∂μ)=if i=j then variance i else 0) :
    (∫ ω, (linear ξ b ω)^2 ∂μ)=∑ i, b i^2*variance i := by
  simp_rw [linear_square_expand]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hij i j).const_mul (b i*b j)))]
  apply Finset.sum_congr rfl; intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => (hij i j).const_mul (b i*b j))]
  simp [integral_const_mul,hc,pow_two]

theorem affine_square_integrable (ξ : ι → Ω → ℝ) (b : ι → ℝ) (a : ℝ)
    (hi : ∀ i, Integrable (ξ i) μ)
    (hij : ∀ i j, Integrable (fun ω => ξ i ω*ξ j ω) μ) :
    Integrable (fun ω => (a-linear ξ b ω)^2) μ := by
  have h : (fun ω => (a-linear ξ b ω)^2) =
      (fun ω => a^2-(2*a)*linear ξ b ω+(linear ξ b ω)^2) := by funext ω; ring
  rw [h]
  exact ((integrable_const _).sub ((linear_integrable μ ξ b hi).const_mul _)).add
    (linear_square_integrable μ ξ b hij)

theorem affine_square_expectation (ξ : ι → Ω → ℝ) (b variance : ι → ℝ) (a : ℝ)
    (hi : ∀ i, Integrable (ξ i) μ)
    (hij : ∀ i j, Integrable (fun ω => ξ i ω*ξ j ω) μ)
    (hm : ∀ i, (∫ ω, ξ i ω ∂μ)=0)
    (hc : ∀ i j, (∫ ω, ξ i ω*ξ j ω ∂μ)=if i=j then variance i else 0) :
    (∫ ω, (a-linear ξ b ω)^2 ∂μ)=a^2+∑ i, b i^2*variance i := by
  have h : (fun ω => (a-linear ξ b ω)^2) =
      (fun ω => a^2-(2*a)*linear ξ b ω+(linear ξ b ω)^2) := by funext ω; ring
  have hs : Integrable (fun ω => a^2-(2*a)*linear ξ b ω) μ :=
    (integrable_const _).sub ((linear_integrable μ ξ b hi).const_mul _)
  rw [h,integral_add hs (linear_square_integrable μ ξ b hij),
    integral_sub (integrable_const _) ((linear_integrable μ ξ b hi).const_mul _),
    integral_const_mul,linear_mean μ ξ b hi hm,linear_second μ ξ b variance hij hc]
  simp
end
end QepFiniteMomentAssembly
