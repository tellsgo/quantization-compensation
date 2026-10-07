import QepGeneralMatrixHistory
import QepGeneralOverloadBridge
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open MeasureTheory QepContinuousCoordinates QepGeneralMatrixDither QepGeneralOverloadBridge
namespace QepRandomOverloadGap
noncomputable section
variable {Ω m n s : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Fintype s]


def loss (k : ℕ) (a Δ : Matrix m n ℝ) (W C : Ω → Matrix m n ℝ)
    (X Z : Ω → Matrix n s ℝ) (α : Ω → ℝ) (p : Ω × Primitive m n) : ℝ :=
  actualLoss k a Δ (target (W p.1) (C p.1) (α p.1)) (W p.1*X p.1) (Z p.1) p.2



theorem all_random_energy (μ : Measure Ω) [SFinite μ] (k : ℕ) (a Δ : Matrix m n ℝ)
    (hΔ : ∀ i j, 0<Δ i j) (W C : Ω → Matrix m n ℝ) (X Z : Ω → Matrix n s ℝ)
    (α : Ω → ℝ)
    (hj : Integrable (loss k a Δ W C X Z α) (μ.prod law))
    (hb : Integrable (fun ω => fSq (A (W ω) (X ω) (Z ω)-α ω • S (C ω) (Z ω)-
      J k a Δ (W ω) (C ω) (Z ω) (α ω))) μ)
    (hn : Integrable (fun ω => noiseEnergy Δ (Z ω)) μ) :
    (∫ p, loss k a Δ W C X Z α p ∂μ.prod law)=
      (∫ ω, fSq (A (W ω) (X ω) (Z ω)-α ω • S (C ω) (Z ω)-
        J k a Δ (W ω) (C ω) (Z ω) (α ω)) ∂μ)+
      (∫ ω, noiseEnergy Δ (Z ω) ∂μ) := by
  have h := QepGeneralMatrixHistory.actual_product_expected_energy μ k a Δ hΔ
    (fun ω => target (W ω) (C ω) (α ω)) (fun ω => W ω*X ω) Z hj
    (by simpa only [actual_bias_residual] using hb) hn
  simpa only [loss,actual_bias_residual] using h




theorem all_random_gram_gap [DecidableEq n] [DecidableEq s]
    (μ : Measure Ω) [SFinite μ] (k : ℕ) (a Δ : Matrix m n ℝ)
    (hΔ : ∀ i j, 0<Δ i j) (W : Ω → Matrix m n ℝ) (X Z : Ω → Matrix n s ℝ)
    (α : ℝ) (hr : ∀ᵐ ω ∂μ, LinearIndependent ℝ (Z ω).row)
    (C : Ω → Matrix m n ℝ) (hC : ∀ ω, C ω=QepGram.correction (W ω) (X ω) (Z ω))
    (hα : Integrable (loss k a Δ W C X Z (fun _ => α)) (μ.prod law))
    (h0 : Integrable (loss k a Δ W C X Z (fun _ => 0)) (μ.prod law))
    (hS : Integrable (fun ω => fSq (S (C ω) (Z ω))) μ)
    (hp : Integrable (fun ω => fInner (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω))
      (J k a Δ (W ω) (C ω) (Z ω) α)) μ)
    (hv : Integrable (fun ω => fSq (J k a Δ (W ω) (C ω) (Z ω) α)) μ)
    (hq : Integrable (fun ω => fInner (A (W ω) (X ω) (Z ω))
      (J k a Δ (W ω) (C ω) (Z ω) 0)) μ)
    (hw : Integrable (fun ω => fSq (J k a Δ (W ω) (C ω) (Z ω) 0)) μ) :
    (∫ p, loss k a Δ W C X Z (fun _ => α) p ∂μ.prod law)-
      (∫ p, loss k a Δ W C X Z (fun _ => 0) p ∂μ.prod law)=
      -α*(2-α)*(∫ ω, fSq (S (C ω) (Z ω)) ∂μ)-
      2*(∫ ω, fInner (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω))
        (J k a Δ (W ω) (C ω) (Z ω) α) ∂μ)+
      (∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) α) ∂μ)+
      2*(∫ ω, fInner (A (W ω) (X ω) (Z ω)) (J k a Δ (W ω) (C ω) (Z ω) 0) ∂μ)-
      (∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) 0) ∂μ) := by
  rw [integral_prod _ hα,integral_prod _ h0,← integral_sub hα.integral_prod_left h0.integral_prod_left]
  have he : (fun ω => (∫ u, loss k a Δ W C X Z (fun _ => α) (ω,u) ∂law)-
      (∫ u, loss k a Δ W C X Z (fun _ => 0) (ω,u) ∂law)) =ᵐ[μ]
      (fun ω => -α*(2-α)*fSq (S (C ω) (Z ω))-
        2*fInner (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω)) (J k a Δ (W ω) (C ω) (Z ω) α)+
        fSq (J k a Δ (W ω) (C ω) (Z ω) α)+
        2*fInner (A (W ω) (X ω) (Z ω)) (J k a Δ (W ω) (C ω) (Z ω) 0)-
        fSq (J k a Δ (W ω) (C ω) (Z ω) 0)) := by
    filter_upwards [hr] with ω hω
    simp only [loss,hC]
    exact actual_projected_gap k a Δ (W ω) hΔ (X ω) (Z ω) hω α
  rw [integral_congr_ae he]
  have hs1 : Integrable (fun ω => -α*(2-α)*fSq (S (C ω) (Z ω))) μ := hS.const_mul _
  have hp1 : Integrable (fun ω => 2*fInner (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω))
      (J k a Δ (W ω) (C ω) (Z ω) α)) μ := hp.const_mul _
  have hq1 : Integrable (fun ω => 2*fInner (A (W ω) (X ω) (Z ω))
      (J k a Δ (W ω) (C ω) (Z ω) 0)) μ := hq.const_mul _
  rw [integral_sub, integral_add, integral_add, integral_sub]
  all_goals try first | assumption | fun_prop
  simp only [integral_const_mul]
theorem matrix_cross_integral_bound (μ : Measure Ω) (R J : Ω → Matrix m s ℝ)
    (hR : MemLp (fun ω => vectorize (R ω)) 2 μ)
    (hJ : MemLp (fun ω => vectorize (J ω)) 2 μ) :
    |∫ ω, fInner (R ω) (J ω) ∂μ| ≤
      Real.sqrt ((∫ ω, fSq (R ω) ∂μ)*(∫ ω, fSq (J ω) ∂μ)) := by
  have h := QepOverloadGap.memLp_cross_sqrt_bound μ
    (fun ω => vectorize (R ω)) (fun ω => vectorize (J ω)) hR hJ
  have he (M : Matrix m s ℝ) : ‖vectorize M‖^2=fSq M :=
    (QepOverloadGap.energy_norm _).symm.trans (vectorize_energy M)
  have hi (M N : Matrix m s ℝ) : inner ℝ (vectorize M) (vectorize N)=fInner M N := vectorize_inner M N
  simpa only [he,hi] using h



theorem all_random_gram_gap_bound [DecidableEq n] [DecidableEq s]
    (μ : Measure Ω) [SFinite μ] (k : ℕ) (a Δ : Matrix m n ℝ)
    (hΔ : ∀ i j, 0<Δ i j) (W : Ω → Matrix m n ℝ) (X Z : Ω → Matrix n s ℝ)
    (α : ℝ) (hr : ∀ᵐ ω ∂μ, LinearIndependent ℝ (Z ω).row)
    (C : Ω → Matrix m n ℝ) (hC : ∀ ω, C ω=QepGram.correction (W ω) (X ω) (Z ω))
    (hα : Integrable (loss k a Δ W C X Z (fun _ => α)) (μ.prod law))
    (h0 : Integrable (loss k a Δ W C X Z (fun _ => 0)) (μ.prod law))
    (hS : Integrable (fun ω => fSq (S (C ω) (Z ω))) μ)
    (hp : Integrable (fun ω => fInner (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω))
      (J k a Δ (W ω) (C ω) (Z ω) α)) μ)
    (hv : Integrable (fun ω => fSq (J k a Δ (W ω) (C ω) (Z ω) α)) μ)
    (hq : Integrable (fun ω => fInner (A (W ω) (X ω) (Z ω))
      (J k a Δ (W ω) (C ω) (Z ω) 0)) μ)
    (hw : Integrable (fun ω => fSq (J k a Δ (W ω) (C ω) (Z ω) 0)) μ)
    (hRα : MemLp (fun ω => vectorize (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω))) 2 μ)
    (hR0 : MemLp (fun ω => vectorize (A (W ω) (X ω) (Z ω))) 2 μ)
    (hJα : MemLp (fun ω => vectorize (J k a Δ (W ω) (C ω) (Z ω) α)) 2 μ)
    (hJ0 : MemLp (fun ω => vectorize (J k a Δ (W ω) (C ω) (Z ω) 0)) 2 μ) :
    |(∫ p, loss k a Δ W C X Z (fun _ => α) p ∂μ.prod law)-
      (∫ p, loss k a Δ W C X Z (fun _ => 0) p ∂μ.prod law)+
      α*(2-α)*(∫ ω, fSq (S (C ω) (Z ω)) ∂μ)| ≤
      2*Real.sqrt ((∫ ω, fSq (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω)) ∂μ)*
        (∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) α) ∂μ))+
      (∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) α) ∂μ)+
      2*Real.sqrt ((∫ ω, fSq (A (W ω) (X ω) (Z ω)) ∂μ)*
        (∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) 0) ∂μ))+
      (∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) 0) ∂μ) := by
  rw [all_random_gram_gap μ k a Δ hΔ W X Z α hr C hC hα h0 hS hp hv hq hw]
  have hv0 : 0 ≤ ∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) α) ∂μ := by
    apply integral_nonneg; intro ω; unfold fSq; positivity
  have hw0 : 0 ≤ ∫ ω, fSq (J k a Δ (W ω) (C ω) (Z ω) 0) ∂μ := by
    apply integral_nonneg; intro ω; unfold fSq; positivity
  have hb := QepOverloadGap.four_term_bound
    (∫ ω, fInner (A (W ω) (X ω) (Z ω)-α • S (C ω) (Z ω)) (J k a Δ (W ω) (C ω) (Z ω) α) ∂μ)
    (∫ ω, fInner (A (W ω) (X ω) (Z ω)) (J k a Δ (W ω) (C ω) (Z ω) 0) ∂μ)
    _ _ hv0 hw0
  have hc := matrix_cross_integral_bound μ _ _ hRα hJα
  have hd := matrix_cross_integral_bound μ _ _ hR0 hJ0
  have he (d p v q w : ℝ) :
      |-α*(2-α)*d-2*p+v+2*q-w+α*(2-α)*d|=|-2*p+v+2*q-w| := by
    congr 1; ring
  rw [he]
  exact hb.trans (by linarith)
end
end QepRandomOverloadGap
