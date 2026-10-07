import QepActualOverloadEvent
import QepGeneralMatrixHistory
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open MeasureTheory QepContinuousCoordinates QepGeneralMatrixDither QepGeneralOverloadBridge
open QepFiniteMomentAssembly
namespace QepRandomOverloadCross
noncomputable section
variable {Ω m n s : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Fintype s]


def errorOutput (k : ℕ) (a Δ T : Matrix m n ℝ) (Z : Matrix n s ℝ)
    (u : Primitive m n) : Matrix m s ℝ := (reconstructed k a Δ T u-T)*Z

theorem error_coordinate_decomposition (k : ℕ) (a Δ T : Matrix m n ℝ)
    (Z : Matrix n s ℝ) (u : Primitive m n) (i : m) (t : s) :
    errorOutput k a Δ T Z u i t=((clipped k a Δ T-T)*Z) i t+
      linear (rowCentered k a Δ T i) (fun j => Z j t) u := by
  have h := actual_coordinate_identity k a Δ T (T*Z) Z i t u
  simp only [errorOutput,Matrix.sub_mul,Matrix.sub_apply]
  linarith

theorem actual_error_coordinate_integrable (k : ℕ) (a Δ T : Matrix m n ℝ)
    (hΔ : ∀ i j,0<Δ i j) (Z : Matrix n s ℝ) (i : m) (t : s) :
    Integrable (fun u => errorOutput k a Δ T Z u i t) law := by
  simp_rw [error_coordinate_decomposition]
  exact (integrable_const _).add (linear_integrable law _ _ (row_moments k a Δ T hΔ i).1)

theorem actual_error_coordinate_mean (k : ℕ) (a Δ T : Matrix m n ℝ)
    (hΔ : ∀ i j,0<Δ i j) (Z : Matrix n s ℝ) (i : m) (t : s) :
    (∫ u, errorOutput k a Δ T Z u i t ∂law)=((clipped k a Δ T-T)*Z) i t := by
  simp_rw [error_coordinate_decomposition]
  have hm := row_moments k a Δ T hΔ i
  rw [integral_add (integrable_const _) (linear_integrable law _ _ hm.1),
    linear_mean law _ _ hm.1 hm.2.2.1]
  simp

theorem actual_cross_integrable (k : ℕ) (a Δ T : Matrix m n ℝ)
    (hΔ : ∀ i j,0<Δ i j) (Z : Matrix n s ℝ) (M : Matrix m s ℝ) :
    Integrable (fun u => fInner M (errorOutput k a Δ T Z u)) law := by
  exact integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun t _ => (actual_error_coordinate_integrable k a Δ T hΔ Z i t).const_mul (M i t)))



theorem actual_cross_mean (k : ℕ) (a Δ T : Matrix m n ℝ)
    (hΔ : ∀ i j,0<Δ i j) (Z : Matrix n s ℝ) (M : Matrix m s ℝ) :
    (∫ u, fInner M (errorOutput k a Δ T Z u) ∂law)=fInner M ((clipped k a Δ T-T)*Z) := by
  unfold fInner
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun t _ => (actual_error_coordinate_integrable k a Δ T hΔ Z i t).const_mul (M i t)))]
  apply Finset.sum_congr rfl; intro i hi
  rw [integral_finsetSum Finset.univ
    (fun t _ => (actual_error_coordinate_integrable k a Δ T hΔ Z i t).const_mul (M i t))]
  simp_rw [integral_const_mul,actual_error_coordinate_mean k a Δ T hΔ]



theorem all_random_noise_cross_eq_bias_cross (μ : Measure Ω) [SFinite μ]
    (k : ℕ) (a Δ : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (W C : Ω → Matrix m n ℝ) (Z : Ω → Matrix n s ℝ) (α : Ω → ℝ)
    (M : Ω → Matrix m s ℝ)
    (hj : Integrable (fun p : Ω × Primitive m n => fInner (M p.1)
      (errorOutput k a Δ (target (W p.1) (C p.1) (α p.1)) (Z p.1) p.2)) (μ.prod law)) :
    (∫ p : Ω × Primitive m n, fInner (M p.1)
      (errorOutput k a Δ (target (W p.1) (C p.1) (α p.1)) (Z p.1) p.2) ∂μ.prod law)=
      ∫ ω, fInner (M ω) (J k a Δ (W ω) (C ω) (Z ω) (α ω)) ∂μ := by
  rw [integral_prod _ hj]
  simp_rw [actual_cross_mean k a Δ _ hΔ]
  rfl



theorem all_random_actual_overload_cross_bound (μ : Measure Ω) [SFinite μ]
    (k : ℕ) (a Δ : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (W C : Ω → Matrix m n ℝ) (Z : Ω → Matrix n s ℝ) (α : Ω → ℝ)
    (hT : Measurable (fun ω => target (W ω) (C ω) (α ω)))
    (hS : MemLp (fun ω => vectorize (S (C ω) (Z ω))) 2 μ)
    (hJ : MemLp (fun ω => vectorize (J k a Δ (W ω) (C ω) (Z ω) (α ω))) 2 μ)
    (hj : Integrable (fun p : Ω × Primitive m n => fInner (S (C p.1) (Z p.1))
      (errorOutput k a Δ (target (W p.1) (C p.1) (α p.1)) (Z p.1) p.2)) (μ.prod law)) :
    |∫ p : Ω × Primitive m n, fInner (S (C p.1) (Z p.1))
      (errorOutput k a Δ (target (W p.1) (C p.1) (α p.1)) (Z p.1) p.2) ∂μ.prod law| ≤
      Real.sqrt ((∫ ω in QepActualOverloadEvent.overload k a Δ
        (fun ω => target (W ω) (C ω) (α ω)), fSq (S (C ω) (Z ω)) ∂μ)*
        (∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) (α ω)) ∂μ)) := by
  have he := all_random_noise_cross_eq_bias_cross μ k a Δ hΔ W C Z α
    (fun ω => S (C ω) (Z ω)) hj
  exact (congrArg abs he).trans_le
    (QepActualOverloadEvent.actual_overload_event_cross_bound μ k a Δ hΔ W C Z α hT hS hJ)
end
end QepRandomOverloadCross
