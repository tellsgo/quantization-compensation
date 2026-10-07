import QepOverloadGap
set_option maxHeartbeats 1400000
set_option linter.unusedVariables false
open QepFiniteDitherLaw QepFiniteDitherMatrix
namespace QepFiniteDitherBridge
noncomputable section

def fInner (A B : Mat) := ∑ i, ∑ j, A i j*B i j
def vectorize (M : Mat) : EuclideanSpace ℝ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun ij => M ij.1 ij.2)

theorem vectorize_energy (M : Mat) : QepOverloadGap.energy (vectorize M)=fSq M := by
  unfold QepOverloadGap.energy
  rw [PiLp.inner_apply]
  change (∑ ij : Fin 2 × Fin 2, M ij.1 ij.2*M ij.1 ij.2)=fSq M
  simp only [Fintype.sum_prod_type,fSq,pow_two]
theorem vectorize_inner (A B : Mat) : QepOverloadGap.cross (vectorize A) (vectorize B)=fInner A B := by
  unfold QepOverloadGap.cross
  rw [PiLp.inner_apply]
  change (∑ ij : Fin 2 × Fin 2, B ij.1 ij.2*A ij.1 ij.2)=fInner A B
  simp only [Fintype.sum_prod_type,fInner,mul_comm]
theorem vectorize_sub (A B : Mat) : vectorize (A-B)=vectorize A-vectorize B := by
  rfl
theorem vectorize_smul (α : ℝ) (A : Mat) : vectorize (α • A)=α • vectorize A := by
  rfl

def A (W X Z : Mat) := W*(X-Z)
def S (C Z : Mat) := C*Z
def target (W C : Mat) (α : ℝ) : Mat := W+α • C
def J (k : ℕ) (W C Z : Mat) (α : ℝ) : Mat := (clipped k (target W C α)-target W C α)*Z

theorem actual_bias_residual (k : ℕ) (W X C Z : Mat) (α : ℝ) :
    W*X-clipped k (target W C α)*Z = A W X Z-α • S C Z-J k W C Z α := by
  unfold A S J target
  simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.mul_sub,Matrix.smul_mul]
  abel

theorem actual_loss_residual (k : ℕ) (W X C Z : Mat) (α : ℝ) :
    expectedLoss k (W*X) (target W C α) Z =
      fSq (A W X Z-α • S C Z-J k W C Z α)+fSq Z/6 := by
  rw [expectedLoss_formula,actual_bias_residual]

theorem matrix_general_gap (A S J J₀ : Mat) (α : ℝ) :
    fSq (A-α • S-J)-fSq (A-J₀) =
      α^2*fSq S-2*α*fInner A S-2*fInner (A-α • S) J+fSq J+2*fInner A J₀-fSq J₀ := by
  have h := QepOverloadGap.general_gap (vectorize A) (vectorize S) (vectorize J) (vectorize J₀) α
  simp only [QepOverloadGap.residual,← vectorize_smul,← vectorize_sub,
    vectorize_energy,vectorize_inner] at h
  exact h

theorem actual_expected_gap (k : ℕ) (W X C Z : Mat) (α : ℝ) :
    expectedLoss k (W*X) (target W C α) Z-expectedLoss k (W*X) (target W C 0) Z =
      α^2*fSq (S C Z)-2*α*fInner (A W X Z) (S C Z)-
      2*fInner (A W X Z-α • S C Z) (J k W C Z α)+fSq (J k W C Z α)+
      2*fInner (A W X Z) (J k W C Z 0)-fSq (J k W C Z 0) := by
  rw [actual_loss_residual,actual_loss_residual]
  simp only [zero_smul,sub_zero]
  rw [add_sub_add_right_eq_sub,matrix_general_gap]

theorem actual_projected_expected_gap (k : ℕ) (W X C Z : Mat) (α : ℝ)
    (hp : fInner (A W X Z) (S C Z)=fSq (S C Z)) :
    expectedLoss k (W*X) (target W C α) Z-expectedLoss k (W*X) (target W C 0) Z =
      -α*(2-α)*fSq (S C Z)-
      2*fInner (A W X Z-α • S C Z) (J k W C Z α)+fSq (J k W C Z α)+
      2*fInner (A W X Z) (J k W C Z 0)-fSq (J k W C Z 0) := by
  rw [actual_expected_gap,hp]; ring

theorem actual_expected_gap_bound (k : ℕ) (W X C Z : Mat) (α : ℝ) :
    |expectedLoss k (W*X) (target W C α) Z-expectedLoss k (W*X) (target W C 0) Z -
      (α^2*fSq (S C Z)-2*α*fInner (A W X Z) (S C Z))| ≤
      2*Real.sqrt (fSq (A W X Z-α • S C Z)*fSq (J k W C Z α))+fSq (J k W C Z α)+
      2*Real.sqrt (fSq (A W X Z)*fSq (J k W C Z 0))+fSq (J k W C Z 0) := by
  have h := QepOverloadGap.general_gap_bound (vectorize (A W X Z)) (vectorize (S C Z))
    (vectorize (J k W C Z α)) (vectorize (J k W C Z 0)) α
  simp only [QepOverloadGap.residual,← vectorize_smul,← vectorize_sub,
    vectorize_energy,vectorize_inner] at h
  rw [actual_loss_residual,actual_loss_residual]
  simpa only [zero_smul,sub_zero,add_sub_add_right_eq_sub] using h

theorem no_overload_zero_bias (k : ℕ) (W C Z : Mat) (α : ℝ)
    (h : ∀ i j, 0 ≤ target W C α i j ∧ target W C α i j ≤ (k:ℝ)) :
    J k W C Z α=0 := by
  have hc : clipped k (target W C α)=target W C α := by
    ext i j
    simp [clipped,clip,min_eq_right (h i j).2,max_eq_right (h i j).1]
  simp [J,hc]
end
end QepFiniteDitherBridge
