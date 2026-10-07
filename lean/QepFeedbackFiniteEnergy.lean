import QepFeedbackConditionalMoments
import QepFeedbackLDL
set_option maxHeartbeats 2400000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackMoments
open QepFeedbackFiniteL2 QepFeedbackConditionalMoments QepFeedbackAlgebra QepFeedbackLDL
namespace QepFeedbackFiniteEnergy
noncomputable section

theorem actual_fresh_square_integrable (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) :
    Integrable (fun p : History (n+1) =>
      (overload (fun i => some (codes i)) origin step weight U n p.1+
       freshInnovation (fun i => some (codes i)) origin step weight U n p)^2) (historyNoise (n+1)) :=
  predictable_square_integrable (historyNoise n) (some (codes n)) _
    (normalizedTarget_measurable _ _ _ _ _ _) _ (finite_overload_memLp codes origin step weight U n) (step n)

theorem actual_fresh_square_expectation (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) :
    (∫ p : History (n+1),
      (overload (fun i => some (codes i)) origin step weight U n p.1+
       freshInnovation (fun i => some (codes i)) origin step weight U n p)^2 ∂historyNoise (n+1)) =
    (∫ p : History n, (overload (fun i => some (codes i)) origin step weight U n p)^2 ∂historyNoise n)+(step n)^2/12 :=
  predictable_square_expectation (historyNoise n) (some (codes n)) _
    (normalizedTarget_measurable _ _ _ _ _ _) _ (finite_overload_memLp codes origin step weight U n) (step n)

theorem weightedDrive_integrable (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (pivot : ℕ → ℝ) (n : ℕ) :
    Integrable (weightedDrive (fun i => some (codes i)) origin step weight U pivot n) (historyNoise n) := by
  induction n with
  | zero => change Integrable (fun p => weightedDrive _ origin step weight U pivot 0 p) _
            simp only [weightedDrive,Fin.sum_univ_zero]; exact integrable_const (0:ℝ)
  | succ n ih =>
    change Integrable (fun p => weightedDrive _ origin step weight U pivot (n+1) p) _
    simp_rw [weightedDrive_succ]
    exact (ih.comp_fst noise).add ((actual_fresh_square_integrable codes origin step weight U n).const_mul (pivot n))

theorem weightedOverload_integrable (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (pivot : ℕ → ℝ) (n : ℕ) :
    Integrable (weightedOverload (fun i => some (codes i)) origin step weight U pivot n) (historyNoise n) := by
  induction n with
  | zero => change Integrable (fun p => weightedOverload _ origin step weight U pivot 0 p) _
            simp only [weightedOverload,Fin.sum_univ_zero]; exact integrable_const (0:ℝ)
  | succ n ih =>
    change Integrable (fun p => weightedOverload _ origin step weight U pivot (n+1) p) _
    simp_rw [weightedOverload_succ]
    exact (ih.comp_fst noise).add
      (((finite_overload_memLp codes origin step weight U n).integrable_sq.const_mul (pivot n)).comp_fst noise)


theorem finite_weighted_energy (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (pivot : ℕ → ℝ) (n : ℕ) :
    (∫ p, weightedDrive (fun i => some (codes i)) origin step weight U pivot n p ∂historyNoise n) =
      (∑ j : Fin n, pivot j.val*(step j.val)^2/12)+
      (∫ p, weightedOverload (fun i => some (codes i)) origin step weight U pivot n p ∂historyNoise n) := by
  induction n with
  | zero => simp [weightedDrive,weightedOverload]
  | succ n ih =>
    simp_rw [weightedDrive_succ,weightedOverload_succ]
    dsimp only [History,historyMeasurable,historyNoise]
    rw [integral_add ((weightedDrive_integrable codes origin step weight U pivot n).comp_fst noise)
      ((actual_fresh_square_integrable codes origin step weight U n).const_mul (pivot n))]
    rw [integral_add ((weightedOverload_integrable codes origin step weight U pivot n).comp_fst noise)
      (((finite_overload_memLp codes origin step weight U n).integrable_sq.const_mul (pivot n)).comp_fst noise)]
    rw [integral_fun_fst (weightedDrive _ origin step weight U pivot n),
        integral_fun_fst (weightedOverload _ origin step weight U pivot n),
        integral_fun_fst (fun p => pivot n*(overload _ origin step weight U n p)^2)]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    have hs := actual_fresh_square_expectation codes origin step weight U n
    dsimp only [History,historyMeasurable,historyNoise] at hs
    rw [integral_const_mul,hs,integral_const_mul,ih,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    ring


theorem actual_finite_matched_output_energy (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j, j ≤ i → U i j=0) (pivot : ℕ → ℝ)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose) :
    (∫ p, rowSq (errorRow (fun i => some (codes i)) origin step weight U n p * Z) ∂historyNoise n) =
      (∑ j : Fin n, pivot j.val*(step j.val)^2/12)+
      (∫ p, weightedOverload (fun i => some (codes i)) origin step weight U pivot n p ∂historyNoise n) := by
  simp_rw [actual_matched_energy _ origin step weight U hU pivot n d Z hgram]
  exact finite_weighted_energy codes origin step weight U pivot n

end
end QepFeedbackFiniteEnergy
