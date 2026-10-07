import QepGram
import QepV1Scalar
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV1
noncomputable section
open scoped BigOperators
open QepCorrected QepGram
variable {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]

section Spectral
open scoped Matrix.Norms.L2Operator

def spectralNorm (A : Mat m n) : ℝ := ‖A‖
theorem spectralNorm_nonneg (A : Mat m n) : 0 ≤ spectralNorm A := norm_nonneg A

theorem spectral_column_bound (A : Mat m n) (B : Mat n t) (j : t) :
    ‖(WithLp.toLp 2 (fun i => (A*B) i j) : EuclideanSpace ℝ m)‖ ≤
      spectralNorm A * ‖(WithLp.toLp 2 (fun i => B i j) : EuclideanSpace ℝ n)‖ := by
  have he : (fun i => (A*B) i j) = A.mulVec (fun i => B i j) := rfl
  rw [he]
  exact Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun i => B i j))
end Spectral

section Frobenius
open scoped Matrix.Norms.Frobenius

def frobNorm (A : Mat m n) : ℝ := ‖A‖
theorem frobNorm_nonneg (A : Mat m n) : 0 ≤ frobNorm A := norm_nonneg A
theorem frobNorm_add_le (A B : Mat m n) : frobNorm (A+B) ≤ frobNorm A+frobNorm B := norm_add_le A B
theorem frobNorm_smul (a : ℝ) (A : Mat m n) : frobNorm (a • A)=|a| *frobNorm A := by
  exact norm_smul a A

theorem frobNorm_sq (A : Mat m n) : (frobNorm A)^2 = fSq A := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_eq_rpow]
  change (Real.sqrt (fSq A))^2 = fSq A
  exact Real.sq_sqrt (fSq_nonneg A)

theorem fSq_columns (A : Mat m n) :
    fSq A = ∑ j, ‖(WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℝ m)‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ∑ j, (A i j)^2) = ∑ j, ∑ i, (A i j)^2
  exact Finset.sum_comm

theorem spectral_frobenius_mul (A : Mat m n) (B : Mat n t) :
    frobNorm (A*B) ≤ spectralNorm A * frobNorm B := by
  have hs : fSq (A*B) ≤ (spectralNorm A)^2 * fSq B := by
    rw [fSq_columns, fSq_columns, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have h := spectral_column_bound A B j
    have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (spectralNorm_nonneg A) (norm_nonneg _)) |>.mpr h
    simpa [mul_pow] using hsq
  rw [← frobNorm_sq, ← frobNorm_sq] at hs
  have ha := frobNorm_nonneg (A*B)
  have hb := mul_nonneg (spectralNorm_nonneg A) (frobNorm_nonneg B)
  nlinarith


theorem frob_projection_contract (A : Mat m t) (P : Mat t t)
    (hs : P.transpose=P) (hp : P*P=P) : frobNorm (A*P) ≤ frobNorm A := by
  have h := QepGram.orthogonal_split A 0 P hs hp (by simp)
  simp only [sub_zero] at h
  have hn := fSq_nonneg (A-A*P)
  have hle : fSq (A*P) ≤ fSq A := by linarith
  rw [← frobNorm_sq, ← frobNorm_sq] at hle
  have h1 := frobNorm_nonneg (A*P)
  have h2 := frobNorm_nonneg A
  nlinarith


theorem frob_complement_contract (A : Mat m t) (P : Mat t t)
    (hs : P.transpose=P) (hp : P*P=P) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    frobNorm (A*(1-a • P)) ≤ frobNorm A := by
  have h := QepCorrected.projected_gap A 0 P hs hp a
  have he : QepCorrected.residual A 0 (A*P) a = A*(1-a • P) := by
    ext i j
    simp [QepCorrected.residual, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  have he0 : QepCorrected.residual A 0 (A*P) 0 = A := by
    ext i j; simp [QepCorrected.residual]
  rw [he,he0] at h
  have hz : fInner (0 : Mat m t) (A*P)=0 := by simp [fInner]
  rw [hz] at h
  have hn : 0 ≤ a*(2-a)*fSq (A*P) := mul_nonneg (mul_nonneg ha0 (by linarith)) (fSq_nonneg _)
  have hle : fSq (A*(1-a • P)) ≤ fSq A := by nlinarith
  rw [← frobNorm_sq, ← frobNorm_sq] at hle
  have h1 := frobNorm_nonneg (A*(1-a • P))
  have h2 := frobNorm_nonneg A
  nlinarith


theorem matrix_preactivation_difference (W E : Mat m n) (X Q B : Mat n t) (a : ℝ) :
    (correctedWeight W X Q a+E)*Q-(W+E)*B =
      W*(Q-B)*(1-a • gramProjection Q)+E*(Q-B)+a • (W*(X-B)*gramProjection Q) := by
  simp only [correctedWeight, Matrix.add_mul, Matrix.smul_mul, correction_times_input]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_assoc, smul_sub]
  abel



theorem matrix_layer_distance (W E : Mat m n) (X Q B : Mat n t)
    (a γ : ℝ) (σ : Mat m t → Mat m t)
    (hgram : IsUnit (gram Q).det) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hγ : 0 ≤ γ)
    (hlip : ∀ U V, frobNorm (σ U-σ V) ≤ γ*frobNorm (U-V)) :
    frobNorm (σ ((correctedWeight W X Q a+E)*Q)-σ ((W+E)*B)) ≤
      γ*(spectralNorm W+spectralNorm E)*frobNorm (Q-B) +
      a*γ*spectralNorm W*frobNorm (X-B) := by
  let P := gramProjection Q
  have hs : P.transpose=P := gramProjection_symmetric Q
  have hp : P*P=P := gramProjection_idempotent Q hgram
  have hleft : frobNorm (W*(Q-B)*(1-a • P)) ≤ spectralNorm W*frobNorm (Q-B) :=
    (frob_complement_contract (W*(Q-B)) P hs hp a ha0 ha1).trans (spectral_frobenius_mul W (Q-B))
  have herr := spectral_frobenius_mul E (Q-B)
  have hcorr : frobNorm (a • (W*(X-B)*P)) ≤ a*spectralNorm W*frobNorm (X-B) := by
    rw [frobNorm_smul,abs_of_nonneg ha0]
    have ht := (frob_projection_contract (W*(X-B)) P hs hp).trans (spectral_frobenius_mul W (X-B))
    have hm := mul_le_mul_of_nonneg_left ht ha0
    simpa [mul_assoc] using hm
  have htri := frobNorm_add_le (W*(Q-B)*(1-a • P)+E*(Q-B)) (a • (W*(X-B)*P))
  have htri2 := frobNorm_add_le (W*(Q-B)*(1-a • P)) (E*(Q-B))
  have hsum : frobNorm (W*(Q-B)*(1-a • P)+E*(Q-B)+a • (W*(X-B)*P)) ≤
      spectralNorm W*frobNorm (Q-B)+spectralNorm E*frobNorm (Q-B)+a*spectralNorm W*frobNorm (X-B) := by
    linarith
  have hout := hlip ((correctedWeight W X Q a+E)*Q) ((W+E)*B)
  rw [matrix_preactivation_difference] at hout
  have hm := mul_le_mul_of_nonneg_left hsum hγ
  change frobNorm (σ ((correctedWeight W X Q a+E)*Q)-σ ((W+E)*B)) ≤ _ at hout
  dsimp [P] at hm
  nlinarith

theorem matrix_layer_distance_of_full_row_rank (W E : Mat m n) (X Q B : Mat n t)
    (a γ : ℝ) (σ : Mat m t → Mat m t)
    (hrow : LinearIndependent ℝ Q.row) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hγ : 0 ≤ γ)
    (hlip : ∀ U V, frobNorm (σ U-σ V) ≤ γ*frobNorm (U-V)) :
    frobNorm (σ ((correctedWeight W X Q a+E)*Q)-σ ((W+E)*B)) ≤
      γ*(spectralNorm W+spectralNorm E)*frobNorm (Q-B) +
      a*γ*spectralNorm W*frobNorm (X-B) :=
  matrix_layer_distance W E X Q B a γ σ (gram_isUnit_det_of_full_row_rank Q hrow)
    ha0 ha1 hγ hlip


section Network
variable (d : ℕ → ℕ) (N L : ℕ)
variable (W E : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
variable (X B Q : (k : ℕ) → Mat (Fin (d k)) (Fin N))
variable (α γ : ℕ → ℝ)
variable (σ : (k : ℕ) → Mat (Fin (d (k+1))) (Fin N) → Mat (Fin (d (k+1))) (Fin N))



theorem matrix_trajectory_recurrence
    (hQ : ∀ k < L, Q (k+1)=σ k ((correctedWeight (W k) (X k) (Q k) (α k)+E k)*Q k))
    (hB : ∀ k < L, B (k+1)=σ k ((W k+E k)*B k))
    (hgram : ∀ k < L, IsUnit (gram (Q k)).det)
    (hα : ∀ k < L, 0 ≤ α k ∧ α k ≤ 1)
    (hγ : ∀ k < L, 0 ≤ γ k)
    (hlip : ∀ k < L, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V)) :
    ∀ k < L, frobNorm (Q (k+1)-B (k+1)) ≤
      γ k*(spectralNorm (W k)+spectralNorm (E k))*frobNorm (Q k-B k) +
      α k*γ k*spectralNorm (W k)*frobNorm (X k-B k) := by
  intro k hk
  rw [hQ k hk,hB k hk]
  exact matrix_layer_distance _ _ _ _ _ _ _ _ (hgram k hk)
    (hα k hk).1 (hα k hk).2 (hγ k hk) (hlip k hk)


theorem matrix_actual_composite
    (hinitB : B 0=X 0) (hinitQ : Q 0=X 0)
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k))
    (hQ : ∀ k < L, Q (k+1)=σ k ((correctedWeight (W k) (X k) (Q k) (α k)+E k)*Q k))
    (hB : ∀ k < L, B (k+1)=σ k ((W k+E k)*B k))
    (hgram : ∀ k < L, IsUnit (gram (Q k)).det)
    (hα : ∀ k < L, 0 ≤ α k ∧ α k ≤ 1)
    (hγ : ∀ k < L, 0 ≤ γ k)
    (hlip : ∀ k < L, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V)) :
    frobNorm (X L-Q L) ≤ weightedBound
      (fun k => γ k*(spectralNorm (W k)+spectralNorm (E k)))
      (fun k => γ k*frobNorm (W k*X k-(W k+E k)*B k)) L := by
  apply cross_terminal_loose
    (fun k => frobNorm (Q k-B k)) (fun k => frobNorm (X k-B k)) (fun k => frobNorm (X k-Q k))
    (fun k => γ k*(spectralNorm (W k)+spectralNorm (E k)))
    (fun k => α k*γ k*spectralNorm (W k))
    (fun k => γ k*frobNorm (W k*X k-(W k+E k)*B k)) L
  · simp [hinitB,hinitQ,frobNorm]
  · simp [hinitB,frobNorm]
  · intro k hk; exact frobNorm_nonneg _
  · intro k hk; exact mul_nonneg (hγ k hk) (add_nonneg (spectralNorm_nonneg _) (spectralNorm_nonneg _))
  · intro k hk
    have h1 := mul_le_mul_of_nonneg_right (hα k hk).2 (mul_nonneg (hγ k hk) (spectralNorm_nonneg (W k)))
    have h2 := mul_nonneg (hγ k hk) (spectralNorm_nonneg (E k))
    nlinarith
  · exact matrix_trajectory_recurrence d N L W E X B Q α γ σ hQ hB hgram hα hγ hlip
  · intro k hk
    rw [hX k hk,hB k hk]
    exact hlip k hk _ _
  · have h := frobNorm_add_le (X L-B L) (B L-Q L)
    rw [sub_add_sub_cancel] at h
    have he : frobNorm (B L-Q L)=frobNorm (Q L-B L) := norm_sub_rev _ _
    rw [he] at h
    exact h



theorem matrix_actual_composite_tight
    (hinitB : B 0=X 0) (hinitQ : Q 0=X 0)
    (hX : ∀ k < L+1, X (k+1)=σ k (W k*X k))
    (hQ : ∀ k < L+1, Q (k+1)=σ k ((correctedWeight (W k) (X k) (Q k) (α k)+E k)*Q k))
    (hB : ∀ k < L+1, B (k+1)=σ k ((W k+E k)*B k))
    (hgram : ∀ k < L+1, IsUnit (gram (Q k)).det)
    (hα : ∀ k < L+1, 0 ≤ α k ∧ α k ≤ 1)
    (hγ : ∀ k < L+1, 0 ≤ γ k)
    (hlip : ∀ k < L+1, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V)) :
    frobNorm (X (L+1)-Q (L+1)) ≤
      γ L*frobNorm (W L*X L-(W L+E L)*B L) + weightedBound
        (fun k => γ (k+1)*(spectralNorm (W (k+1))+spectralNorm (E (k+1))))
        (fun k => (α (k+1)*γ (k+1)*spectralNorm (W (k+1)))*
          (γ k*frobNorm (W k*X k-(W k+E k)*B k))) L := by
  have hr := matrix_trajectory_recurrence d N (L+1) W E X B Q α γ σ hQ hB hgram hα hγ hlip
  apply cross_terminal_tight
    (fun k => frobNorm (Q k-B k)) (fun k => frobNorm (X k-B k)) (fun k => frobNorm (X k-Q k))
    (fun k => γ k*(spectralNorm (W k)+spectralNorm (E k)))
    (fun k => α k*γ k*spectralNorm (W k))
    (fun k => γ k*frobNorm (W k*X k-(W k+E k)*B k)) L
  · have h := hr 0 (by omega)
    simpa [hinitB,hinitQ,frobNorm] using h
  · intro k hk; exact mul_nonneg (hγ k hk) (add_nonneg (spectralNorm_nonneg _) (spectralNorm_nonneg _))
  · intro k hk; exact mul_nonneg (mul_nonneg (hα k hk).1 (hγ k hk)) (spectralNorm_nonneg _)
  · exact hr
  · intro k hk
    rw [hX k hk,hB k hk]
    exact hlip k hk _ _
  · have h := frobNorm_add_le (X (L+1)-B (L+1)) (B (L+1)-Q (L+1))
    rw [sub_add_sub_cancel] at h
    have he : frobNorm (B (L+1)-Q (L+1))=frobNorm (Q (L+1)-B (L+1)) := norm_sub_rev _ _
    rw [he] at h
    exact h
end Network
end Frobenius
end
end QepV1
