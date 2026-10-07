import QepFeedbackAlgebra
import QepFeedbackMoments
set_option maxHeartbeats 2200000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra QepFeedbackMoments
namespace QepFeedbackEnergy
noncomputable section

theorem noiseVector_coordinates (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) (j : Fin n) :
    noiseVector mode origin step weight U n p j = step j.val *
      coordinates n (causalInnovations mode (normalizedTarget mode origin step weight U) n p) j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [noiseVector,coordinates,causalInnovations,freshInnovation]
    · simpa only [noiseVector,coordinates,causalInnovations,Fin.snoc_castSucc,Fin.val_castSucc] using ih p.1 i

theorem unbounded_overloadVector_zero (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hstep : ∀ n, step n ≠ 0) (n : ℕ) (p : History n) (j : Fin n) :
    overloadVector (fun _ => none) origin step weight U n p j = 0 := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [overloadVector,Fin.snoc_last] using unbounded_overload_zero origin step weight U hstep n p.1
    · simpa only [overloadVector,Fin.snoc_castSucc] using ih p.1 i

def coefficients {n d : ℕ} (step : ℕ → ℝ) (M : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) (i : ℕ) : ℝ :=
  if hi : i<n then step i * M ⟨i,hi⟩ k else 0


theorem actual_output_as_linear (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hU : ∀ i j, j ≤ i → U i j = 0) (hstep : ∀ n,step n ≠ 0)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (p : History n) (k : Fin d) :
    (errorRow (fun _ => none) origin step weight U n p * Z) () k =
      linear (coefficients step ((triangle U n)⁻¹ * Z) k) n
        (causalInnovations (fun _ => none) (normalizedTarget (fun _ => none) origin step weight U) n p) := by
  rw [actual_error_inverse_filter _ _ _ _ _ hU,Matrix.mul_assoc,linear_sum]
  simp only [Matrix.mul_apply,drivingRow]
  apply Finset.sum_congr rfl
  intro i _
  rw [driving_split,unbounded_overloadVector_zero origin step weight U hstep,add_zero,
    noiseVector_coordinates]
  simp only [coefficients,dif_pos i.isLt,Matrix.mul_apply]
  ring

theorem actual_output_mean (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hU : ∀ i j, j ≤ i → U i j = 0) (hstep : ∀ n,step n ≠ 0)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    (∫ p, (errorRow (fun _ => none) origin step weight U n p * Z) () k ∂historyNoise n)=0 := by
  simp_rw [actual_output_as_linear origin step weight U hU hstep n d Z]
  exact actual_linear_mean _ _ (normalizedTarget_measurable _ _ _ _ _) _ _

theorem actual_output_second (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hU : ∀ i j, j ≤ i → U i j = 0) (hstep : ∀ n,step n ≠ 0)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    (∫ p, ((errorRow (fun _ => none) origin step weight U n p * Z) () k)^2 ∂historyNoise n)=
      ∑ i : Fin n, (step i.val)^2/12 * (((triangle U n)⁻¹ * Z) i k)^2 := by
  simp_rw [actual_output_as_linear origin step weight U hU hstep n d Z]
  rw [actual_linear_second _ _ (normalizedTarget_measurable _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coefficients,dif_pos i.isLt,Matrix.mul_apply]
  ring



theorem current_target_energy_independent (origin step weight₁ weight₂ : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j, j ≤ i → U i j = 0) (hstep : ∀ n,step n ≠ 0)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    (∫ p, ((errorRow (fun _ => none) origin step weight₁ U n p * Z) () k)^2 ∂historyNoise n)=
    (∫ p, ((errorRow (fun _ => none) origin step weight₂ U n p * Z) () k)^2 ∂historyNoise n) := by
  rw [actual_output_second origin step weight₁ U hU hstep,actual_output_second origin step weight₂ U hU hstep]

end
end QepFeedbackEnergy
