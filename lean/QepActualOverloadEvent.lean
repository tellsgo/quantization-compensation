import QepGeneralOverloadBridge
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open MeasureTheory QepFiniteDitherLaw QepGeneralMatrixDither QepGeneralOverloadBridge
namespace QepActualOverloadEvent
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω m n s : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Fintype s]

def overload (k : ℕ) (a Δ : Matrix m n ℝ) (T : Ω → Matrix m n ℝ) : Set Ω :=
  {ω | ∃ i j, T ω i j<a i j ∨ a i j+Δ i j*k<T ω i j}

theorem overload_measurable (k : ℕ) (a Δ : Matrix m n ℝ)
    (T : Ω → Matrix m n ℝ) (hT : Measurable T) : MeasurableSet (overload k a Δ T) := by
  unfold overload
  simp_rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  have ht := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hT)
  exact (measurableSet_lt ht measurable_const).union (measurableSet_lt measurable_const ht)

theorem actual_bias_supported (k : ℕ) (a Δ : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (W C : Ω → Matrix m n ℝ) (Z : Ω → Matrix n s ℝ) (α : Ω → ℝ) (ω : Ω)
    (h : ω ∉ overload k a Δ (fun ω => target (W ω) (C ω) (α ω))) :
    J k a Δ (W ω) (C ω) (Z ω) (α ω)=0 := by
  have hr : ∀ i j, a i j≤target (W ω) (C ω) (α ω) i j ∧
      target (W ω) (C ω) (α ω) i j≤a i j+Δ i j*k := by
    simpa only [overload,Set.mem_ofPred_eq,not_exists,not_or,not_lt] using h
  exact no_overload_zero_bias k a Δ (W ω) (C ω) hΔ (Z ω) (α ω) hr

theorem vectorize_norm_sq (M : Matrix m s ℝ) : ‖vectorize M‖^2=fSq M :=
  (QepOverloadGap.energy_norm (vectorize M)).symm.trans (vectorize_energy M)



theorem actual_overload_event_cross_bound (μ : Measure Ω) (k : ℕ) (a Δ : Matrix m n ℝ)
    (hΔ : ∀ i j,0<Δ i j) (W C : Ω → Matrix m n ℝ) (Z : Ω → Matrix n s ℝ)
    (α : Ω → ℝ) (hT : Measurable (fun ω => target (W ω) (C ω) (α ω)))
    (hS : MemLp (fun ω => vectorize (S (C ω) (Z ω))) 2 μ)
    (hJ : MemLp (fun ω => vectorize (J k a Δ (W ω) (C ω) (Z ω) (α ω))) 2 μ) :
    |∫ ω, fInner (S (C ω) (Z ω)) (J k a Δ (W ω) (C ω) (Z ω) (α ω)) ∂μ| ≤
      Real.sqrt ((∫ ω in overload k a Δ (fun ω => target (W ω) (C ω) (α ω)),
        fSq (S (C ω) (Z ω)) ∂μ)*(∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) (α ω)) ∂μ)) := by
  have hz : ∀ᵐ ω ∂μ, ω∉overload k a Δ (fun ω => target (W ω) (C ω) (α ω)) →
      vectorize (J k a Δ (W ω) (C ω) (Z ω) (α ω))=0 := by
    apply Filter.Eventually.of_forall; intro ω h
    rw [actual_bias_supported k a Δ hΔ W C Z α ω h]
    rfl
  have hb := QepOverloadGap.overload_event_cross_bound μ
    (fun ω => vectorize (S (C ω) (Z ω)))
    (fun ω => vectorize (J k a Δ (W ω) (C ω) (Z ω) (α ω))) hS hJ
    (overload k a Δ (fun ω => target (W ω) (C ω) (α ω))) (overload_measurable k a Δ _ hT) hz
  simp only [vectorize_norm_sq] at hb
  have hi (M N : Matrix m s ℝ) : inner ℝ (vectorize M) (vectorize N)=fInner M N := vectorize_inner M N
  simpa only [hi] using hb
end
end QepActualOverloadEvent
