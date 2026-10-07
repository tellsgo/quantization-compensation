import QepFeedbackFiniteEnergy
import QepFeedbackCovariance
set_option maxHeartbeats 2400000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra
open QepFeedbackMoments QepFeedbackEnergy QepFeedbackFiniteL2 QepFeedbackFiniteEnergy
open QepFeedbackCovariance QepFeedbackConditionalMoments QepFeedbackLDL
namespace QepFeedbackBias
noncomputable section

def noiseRow (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (n : ℕ) (p : History n) : Row n := fun _ j => noiseVector mode origin step weight U n p j
def overloadRow (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (n : ℕ) (p : History n) : Row n := fun _ j => overloadVector mode origin step weight U n p j

theorem noise_output_linear (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (M : Matrix (Fin n) (Fin d) ℝ) (p : History n) (k : Fin d) :
    (noiseRow mode origin step weight U n p*M) () k =
    linear (coefficients step M k) n (causalInnovations mode (normalizedTarget mode origin step weight U) n p) := by
  rw [linear_sum,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _; simp only [noiseRow,noiseVector_coordinates,coefficients,dif_pos j.isLt]; ring

theorem noise_output_mean (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (M : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    (∫ p,(noiseRow mode origin step weight U n p*M) () k ∂historyNoise n)=0 := by
  simp_rw [noise_output_linear]
  exact actual_linear_mean _ _ (normalizedTarget_measurable _ _ _ _ _) _ _

theorem noise_output_integrable (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (M : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    Integrable (fun p => (noiseRow mode origin step weight U n p*M) () k) (historyNoise n) := by
  simp_rw [noise_output_linear]
  exact (causal_innovations_measurePreserving _ _ (normalizedTarget_measurable _ _ _ _ _) n).integrable_comp_of_integrable
    (linear_integrable _ n)

theorem finite_overloadVector_memLp (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (j : Fin n) :
    MemLp (fun p => overloadVector (fun i => some (codes i)) origin step weight U n p j) 2 (historyNoise n) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [overloadVector,Fin.snoc_last]
      exact (finite_overload_memLp codes origin step weight U n).comp_measurePreserving
        (measurePreserving_fst (μ:=historyNoise n) (ν:=noise))
    · simp only [overloadVector,Fin.snoc_castSucc]
      exact (ih i).comp_measurePreserving (measurePreserving_fst (μ:=historyNoise n) (ν:=noise))

theorem finite_overload_output_integrable (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (M : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    Integrable (fun p => (overloadRow (fun i => some (codes i)) origin step weight U n p*M) () k) (historyNoise n) := by
  simp only [Matrix.mul_apply,overloadRow]
  exact integrable_finsetSum _ (fun j _ =>
    (MemLp.integrable (by norm_num) (finite_overloadVector_memLp codes origin step weight U n j)).mul_const _)

theorem actual_output_split (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0) (n d : ℕ)
    (Z : Matrix (Fin n) (Fin d) ℝ) (p : History n) :
    errorRow mode origin step weight U n p*Z =
    noiseRow mode origin step weight U n p*((triangle U n)⁻¹*Z)+
    overloadRow mode origin step weight U n p*((triangle U n)⁻¹*Z) := by
  rw [actual_error_inverse_filter _ _ _ _ _ hU,Matrix.mul_assoc,← Matrix.add_mul]
  congr 1
  ext i j; exact driving_split _ _ _ _ _ _ _ _


theorem actual_finite_output_mean (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0) (n d : ℕ)
    (Z : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    (∫ p,(errorRow (fun i => some (codes i)) origin step weight U n p*Z) () k ∂historyNoise n)=
    (∫ p,(overloadRow (fun i => some (codes i)) origin step weight U n p*((triangle U n)⁻¹*Z)) () k ∂historyNoise n) := by
  simp_rw [actual_output_split _ origin step weight U hU n d Z,Matrix.add_apply]
  rw [integral_add (noise_output_integrable _ origin step weight U n d _ k)
    (finite_overload_output_integrable codes origin step weight U n d _ k),noise_output_mean,zero_add]

end
end QepFeedbackBias
