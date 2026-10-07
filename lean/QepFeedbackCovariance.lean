import QepFeedbackEnergy
import QepFeedbackConditionalMoments
import QepFeedbackLDL
set_option maxHeartbeats 2000000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra
open QepFeedbackMoments QepFeedbackEnergy QepFeedbackConditionalMoments QepFeedbackLDL
namespace QepFeedbackCovariance
noncomputable section

theorem linear_add (a b : ℕ → ℝ) (n : ℕ) (p : History n) :
    linear (fun i => a i+b i) n p=linear a n p+linear b n p := by
  induction n with
  | zero => simp [linear]
  | succ n ih => simp only [linear,ih]; ring

theorem linear_cross_integrable (a b : ℕ → ℝ) (n : ℕ) :
    Integrable (fun p => linear a n p*linear b n p) (historyNoise n) := by
  have h := (((linear_square_integrable (fun i => a i+b i) n).sub
    (linear_square_integrable a n)).sub (linear_square_integrable b n)).div_const 2
  convert h using 1
  funext p; simp only [Pi.sub_apply,linear_add]; ring

theorem linear_cross (a b : ℕ → ℝ) (n : ℕ) :
    (∫ p, linear a n p*linear b n p ∂historyNoise n)=∑ i : Fin n, a i.val*b i.val/12 := by
  have heq : (fun p => linear a n p*linear b n p) =
    (fun p => ((linear (fun i => a i+b i) n p)^2-(linear a n p)^2-(linear b n p)^2)/2) := by
    funext p; rw [linear_add]; ring
  have ha : Integrable (fun p => (linear (fun i => a i+b i) n p)^2-(linear a n p)^2) (historyNoise n) :=
    (linear_square_integrable _ n).sub (linear_square_integrable _ n)
  rw [heq,integral_div,integral_sub ha (linear_square_integrable b n),
    integral_sub (linear_square_integrable (fun i => a i+b i) n) (linear_square_integrable a n)]
  simp only [linear_second,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem actual_output_square_integrable (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hU : ∀ i j, j ≤ i → U i j=0) (hstep : ∀ n,step n≠0)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    Integrable (fun p => ((errorRow (fun _ => none) origin step weight U n p*Z) () k)^2) (historyNoise n) := by
  simp_rw [actual_output_as_linear origin step weight U hU hstep n d Z]
  exact (causal_innovations_measurePreserving _ _ (normalizedTarget_measurable _ _ _ _ _) n).integrable_comp_of_integrable
    (linear_square_integrable _ n)


theorem actual_output_cross (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hU : ∀ i j, j ≤ i → U i j=0) (hstep : ∀ n,step n≠0)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (k l : Fin d) :
    (∫ p, (errorRow (fun _ => none) origin step weight U n p*Z) () k*
      (errorRow (fun _ => none) origin step weight U n p*Z) () l ∂historyNoise n)=
      ∑ i : Fin n, (step i.val)^2/12*(((triangle U n)⁻¹*Z) i k)*(((triangle U n)⁻¹*Z) i l) := by
  simp_rw [actual_output_as_linear origin step weight U hU hstep n d Z]
  rw [integral_of_preserving (causal_innovations_measurePreserving _ _ (normalizedTarget_measurable _ _ _ _ _) n)
    _ (linear_cross_integrable _ _ n),linear_cross]
  apply Finset.sum_congr rfl
  intro i _; simp only [coefficients,dif_pos i.isLt]; ring


theorem actual_output_energy (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hU : ∀ i j, j ≤ i → U i j=0) (hstep : ∀ n,step n≠0)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) :
    (∫ p, rowSq (errorRow (fun _ => none) origin step weight U n p*Z) ∂historyNoise n)=
      ∑ k : Fin d, ∑ i : Fin n, (step i.val)^2/12*(((triangle U n)⁻¹*Z) i k)^2 := by
  unfold rowSq
  rw [integral_finsetSum Finset.univ (fun k _ => actual_output_square_integrable origin step weight U hU hstep n d Z k)]
  simp_rw [actual_output_second origin step weight U hU hstep n d Z]

end
end QepFeedbackCovariance
