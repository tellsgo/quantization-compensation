import QepGeneralMatrixDither
import QepOverloadGap
import QepGram
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open MeasureTheory QepFiniteDitherLaw QepContinuousCoordinates QepGeneralMatrixDither
namespace QepGeneralOverloadBridge
noncomputable section
attribute [local instance] Classical.propDecidable
variable {m n s : Type*} [Fintype m] [Fintype n] [Fintype s]

def fInner (A B : Matrix m s ℝ) := ∑ i, ∑ j, A i j*B i j
def vectorize (M : Matrix m s ℝ) : EuclideanSpace ℝ (m×s) := WithLp.toLp 2 (fun ij => M ij.1 ij.2)
theorem vectorize_energy (M : Matrix m s ℝ) : QepOverloadGap.energy (vectorize M)=fSq M := by
  unfold QepOverloadGap.energy
  rw [PiLp.inner_apply]
  change (∑ ij : m×s, M ij.1 ij.2*M ij.1 ij.2)=fSq M
  simp only [Fintype.sum_prod_type,fSq,pow_two]
theorem vectorize_inner (A B : Matrix m s ℝ) : QepOverloadGap.cross (vectorize A) (vectorize B)=fInner A B := by
  unfold QepOverloadGap.cross
  rw [PiLp.inner_apply]
  change (∑ ij : m×s, B ij.1 ij.2*A ij.1 ij.2)=fInner A B
  simp only [Fintype.sum_prod_type,fInner,mul_comm]
theorem vectorize_sub (A B : Matrix m s ℝ) : vectorize (A-B)=vectorize A-vectorize B := rfl
theorem vectorize_smul (α : ℝ) (A : Matrix m s ℝ) : vectorize (α • A)=α • vectorize A := rfl

def A (W : Matrix m n ℝ) (X Z : Matrix n s ℝ) := W*(X-Z)
def S (C : Matrix m n ℝ) (Z : Matrix n s ℝ) := C*Z
def target (W C : Matrix m n ℝ) (α : ℝ) := W+α • C
def J (k : ℕ) (a Δ W C : Matrix m n ℝ) (Z : Matrix n s ℝ) (α : ℝ) :=
  (clipped k a Δ (target W C α)-target W C α)*Z
def expected (k : ℕ) (a Δ W C : Matrix m n ℝ) (X Z : Matrix n s ℝ) (α : ℝ) :=
  ∫ u, actualLoss k a Δ (target W C α) (W*X) Z u ∂law

theorem actual_bias_residual (k : ℕ) (a Δ W C : Matrix m n ℝ) (X Z : Matrix n s ℝ) (α : ℝ) :
    W*X-clipped k a Δ (target W C α)*Z=A W X Z-α • S C Z-J k a Δ W C Z α := by
  unfold A S J target
  simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.mul_sub,Matrix.smul_mul]
  abel

theorem actual_loss_residual (k : ℕ) (a Δ W C : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (X Z : Matrix n s ℝ) (α : ℝ) :
    expected k a Δ W C X Z α=fSq (A W X Z-α • S C Z-J k a Δ W C Z α)+noiseEnergy Δ Z := by
  unfold expected
  rw [actual_matrix_expected_loss k a Δ _ hΔ,actual_bias_residual]

theorem matrix_general_gap (A S J J₀ : Matrix m s ℝ) (α : ℝ) :
    fSq (A-α • S-J)-fSq (A-J₀)=α^2*fSq S-2*α*fInner A S-
      2*fInner (A-α • S) J+fSq J+2*fInner A J₀-fSq J₀ := by
  have h := QepOverloadGap.general_gap (vectorize A) (vectorize S) (vectorize J) (vectorize J₀) α
  simp only [QepOverloadGap.residual,← vectorize_smul,← vectorize_sub,vectorize_energy,vectorize_inner] at h
  exact h

theorem actual_expected_gap (k : ℕ) (a Δ W C : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (X Z : Matrix n s ℝ) (α : ℝ) :
    expected k a Δ W C X Z α-expected k a Δ W C X Z 0=
      α^2*fSq (S C Z)-2*α*fInner (A W X Z) (S C Z)-
      2*fInner (A W X Z-α • S C Z) (J k a Δ W C Z α)+fSq (J k a Δ W C Z α)+
      2*fInner (A W X Z) (J k a Δ W C Z 0)-fSq (J k a Δ W C Z 0) := by
  rw [actual_loss_residual k a Δ W C hΔ,actual_loss_residual k a Δ W C hΔ]
  simp only [zero_smul,sub_zero]
  rw [add_sub_add_right_eq_sub,matrix_general_gap]

theorem gram_actual_projection_identity [DecidableEq n] [DecidableEq s]
    (W : Matrix m n ℝ) (X Z : Matrix n s ℝ) (hr : LinearIndependent ℝ Z.row) :
    fInner (A W X Z) (S (QepGram.correction W X Z) Z)=fSq (S (QepGram.correction W X Z) Z) := by
  unfold A S
  rw [QepGram.correction_times_input]
  exact QepCorrected.projection_inner _ _ (QepGram.gramProjection_symmetric Z)
    (QepGram.gramProjection_idempotent Z (QepGram.gram_isUnit_det_of_full_row_rank Z hr))

theorem actual_projected_gap [DecidableEq n] [DecidableEq s]
    (k : ℕ) (a Δ W : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (X Z : Matrix n s ℝ) (hr : LinearIndependent ℝ Z.row) (α : ℝ) :
    let C := QepGram.correction W X Z
    expected k a Δ W C X Z α-expected k a Δ W C X Z 0=
      -α*(2-α)*fSq (S C Z)-
      2*fInner (A W X Z-α • S C Z) (J k a Δ W C Z α)+fSq (J k a Δ W C Z α)+
      2*fInner (A W X Z) (J k a Δ W C Z 0)-fSq (J k a Δ W C Z 0) := by
  dsimp only
  rw [actual_expected_gap k a Δ W _ hΔ,gram_actual_projection_identity W X Z hr]
  ring

theorem actual_expected_gap_bound (k : ℕ) (a Δ W C : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (X Z : Matrix n s ℝ) (α : ℝ) :
    |expected k a Δ W C X Z α-expected k a Δ W C X Z 0-
      (α^2*fSq (S C Z)-2*α*fInner (A W X Z) (S C Z))| ≤
      2*Real.sqrt (fSq (A W X Z-α • S C Z)*fSq (J k a Δ W C Z α))+fSq (J k a Δ W C Z α)+
      2*Real.sqrt (fSq (A W X Z)*fSq (J k a Δ W C Z 0))+fSq (J k a Δ W C Z 0) := by
  have h := QepOverloadGap.general_gap_bound (vectorize (A W X Z)) (vectorize (S C Z))
    (vectorize (J k a Δ W C Z α)) (vectorize (J k a Δ W C Z 0)) α
  simp only [QepOverloadGap.residual,← vectorize_smul,← vectorize_sub,vectorize_energy,vectorize_inner] at h
  rw [actual_loss_residual k a Δ W C hΔ,actual_loss_residual k a Δ W C hΔ]
  simpa only [zero_smul,sub_zero,add_sub_add_right_eq_sub] using h

theorem no_overload_zero_bias (k : ℕ) (a Δ W C : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (Z : Matrix n s ℝ) (α : ℝ)
    (h : ∀ i j, a i j≤target W C α i j ∧ target W C α i j≤a i j+Δ i j*k) :
    J k a Δ W C Z α=0 := by
  have hc : clipped k a Δ (target W C α)=target W C α := by
    ext i j
    simp only [clipped,scaled_clip_is_interval_clip _ _ (hΔ i j),
      min_eq_right (h i j).2,max_eq_right (h i j).1]
  simp [J,hc]
end
end QepGeneralOverloadBridge
