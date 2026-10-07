import QepX1NetworkMoments

set_option autoImplicit false
namespace QepX1
noncomputable section
open MeasureTheory QepCorrected QepGram QepV3
open scoped BigOperators
variable {Ω m n : Type*} [Fintype Ω] [Fintype m] [Fintype n]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]


theorem probability_atoms_form_law (μ : Measure Ω) [IsProbabilityMeasure μ] :
    FiniteLaw (fun ω => μ.real {ω}) := by
  constructor
  · intro ω; exact measureReal_nonneg
  · simp


theorem finite_mean_entry_integral (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Ω → Mat m n) (i : m) (j : n) :
    mean (fun ω => μ.real {ω}) F i j = ∫ ω,F ω i j ∂μ := by
  rw [integral_fintype Integrable.of_finite,mean_apply]
  rfl

theorem finite_fSq_integral (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → Mat m n) :
    (∑ ω, μ.real {ω}*fSq (F ω)) = ∫ ω,fSq (F ω) ∂μ := by
  rw [integral_fintype Integrable.of_finite]
  rfl




theorem finite_actual_output_square_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ → ℕ) (N : ℕ)
    (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (X0 : Mat (Fin (d 0)) (Fin N)) (a : ℕ → ℝ)
    (E : (k : ℕ) → Ω → Mat (Fin (d (k+1))) (Fin (d k))) (k : ℕ) :
    Integrable (fun ω => fSq (student d N W X0 a E k ω)) μ :=
  Integrable.of_finite

theorem finite_actual_error_square_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ → ℕ) (N : ℕ)
    (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (X0 : Mat (Fin (d 0)) (Fin N)) (a : ℕ → ℝ)
    (E : (k : ℕ) → Ω → Mat (Fin (d (k+1))) (Fin (d k))) (k : ℕ) :
    Integrable (fun ω => fSq (error d N W X0 a E k ω)) μ :=
  Integrable.of_finite

end
end QepX1
