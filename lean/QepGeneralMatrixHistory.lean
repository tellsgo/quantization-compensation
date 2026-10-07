import QepGeneralMatrixDither
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
open MeasureTheory QepFiniteDitherLaw QepFiniteDitherHistory QepContinuousCoordinates
namespace QepGeneralMatrixHistory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω m n s : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Fintype s]



theorem actual_standardized_history_law (μ : Measure Ω) [SFinite μ] (k : ℕ)
    (a Δ : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j) (T : Ω → Matrix m n ℝ) (hT : Measurable T) :
    Measure.map (fun p : Ω × ((m×n)→ℝ) => (p.1,fun (ij : m×n) =>
      (QepGeneralMatrixDither.reconstructed k a Δ (T p.1) p.2 ij.1 ij.2-
       QepGeneralMatrixDither.clipped k a Δ (T p.1) ij.1 ij.2)/Δ ij.1 ij.2))
      (μ.prod law)=μ.prod law := by
  have ht : Measurable (fun ω (ij : m×n) => (T ω ij.1 ij.2-a ij.1 ij.2)/Δ ij.1 ij.2) := by
    apply measurable_pi_iff.mpr; intro ij
    exact (((measurable_pi_apply ij.2).comp ((measurable_pi_apply ij.1).comp hT)).sub measurable_const).div_const _
  have hf : (fun p : Ω × ((m×n)→ℝ) => (p.1,fun (ij : m×n) =>
      (QepGeneralMatrixDither.reconstructed k a Δ (T p.1) p.2 ij.1 ij.2-
       QepGeneralMatrixDither.clipped k a Δ (T p.1) ij.1 ij.2)/Δ ij.1 ij.2)) =
    (fun p : Ω × ((m×n)→ℝ) => (p.1,fun (ij : m×n) => reconstruction k
      ((T p.1 ij.1 ij.2-a ij.1 ij.2)/Δ ij.1 ij.2) (p.2 ij)-
      clip k ((T p.1 ij.1 ij.2-a ij.1 ij.2)/Δ ij.1 ij.2))) := by
    funext p
    congr 1
    funext ij
    change (scaledReconstruction _ _ _ _ _-scaledClip _ _ _ _)/_= _
    rw [scaled_reconstruction_identity _ _ (ne_of_gt (hΔ ij.1 ij.2))]
    exact mul_div_cancel_left₀ _ (ne_of_gt (hΔ ij.1 ij.2))
  exact (congrArg (fun f => Measure.map f (μ.prod law)) hf).trans
    (history_finite_family_joint_law μ k (fun ω (ij : m×n) => (T ω ij.1 ij.2-a ij.1 ij.2)/Δ ij.1 ij.2) ht)

open QepGeneralMatrixDither

theorem actual_history_inner_energy (k : ℕ) (a Δ : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (T : Ω → Matrix m n ℝ) (Y : Ω → Matrix m s ℝ) (Z : Ω → Matrix n s ℝ) (ω : Ω) :
    (∫ u, actualLoss k a Δ (T ω) (Y ω) (Z ω) u ∂law)=
      fSq (Y ω-clipped k a Δ (T ω)*Z ω)+noiseEnergy Δ (Z ω) :=
  actual_matrix_expected_loss k a Δ (T ω) hΔ (Y ω) (Z ω)


theorem actual_product_expected_energy (μ : Measure Ω) [SFinite μ] (k : ℕ)
    (a Δ : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (T : Ω → Matrix m n ℝ) (Y : Ω → Matrix m s ℝ) (Z : Ω → Matrix n s ℝ)
    (hj : Integrable (fun p : Ω × ((m×n)→ℝ) => actualLoss k a Δ (T p.1) (Y p.1) (Z p.1) p.2) (μ.prod law))
    (hb : Integrable (fun ω => fSq (Y ω-clipped k a Δ (T ω)*Z ω)) μ)
    (hn : Integrable (fun ω => noiseEnergy Δ (Z ω)) μ) :
    (∫ p : Ω × ((m×n)→ℝ), actualLoss k a Δ (T p.1) (Y p.1) (Z p.1) p.2 ∂μ.prod law)=
      (∫ ω, fSq (Y ω-clipped k a Δ (T ω)*Z ω) ∂μ)+(∫ ω, noiseEnergy Δ (Z ω) ∂μ) := by
  rw [integral_prod _ hj]
  simp_rw [actual_matrix_expected_loss k a Δ _ hΔ]
  exact integral_add hb hn
end
end QepGeneralMatrixHistory
