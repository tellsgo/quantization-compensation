import QepV1Remainder

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV1
noncomputable section
open QepCorrected QepGram
open scoped Matrix.Norms.Frobenius


theorem base_residual_envelope {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (W E : Mat m n) (X B : Mat n p) :
    frobNorm (W*X-(W+E)*B) ≤
      (spectralNorm W+spectralNorm E)*frobNorm (X-B)+spectralNorm E*frobNorm X := by
  have he : W*X-(W+E)*B = W*(X-B)+E*(X-B)+ -(E*X) := by
    simp only [Matrix.mul_sub,Matrix.add_mul]; abel
  rw [he]
  have ht := frobNorm_add_le (W*(X-B)+E*(X-B)) (-(E*X))
  have ht2 := frobNorm_add_le (W*(X-B)) (E*(X-B))
  have hn : frobNorm (-(E*X))=frobNorm (E*X) := norm_neg _
  rw [hn] at ht
  have h1 := spectral_frobenius_mul W (X-B)
  have h2 := spectral_frobenius_mul E (X-B)
  have h3 := spectral_frobenius_mul E X
  nlinarith

variable (d : ℕ → ℕ) (N L : ℕ)
variable (W E : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
variable (X B Q : (k : ℕ) → Mat (Fin (d k)) (Fin N))
variable (α γ f : ℕ → ℝ)
variable (σ : (k : ℕ) → Mat (Fin (d (k+1))) (Fin N) → Mat (Fin (d (k+1))) (Fin N))



def baseEnvelope : ℕ → ℝ := weightedBound
  (fun k => γ k*(spectralNorm (W k)+f k)) (fun k => γ k*f k*frobNorm (X k))

def residualEnvelope (k : ℕ) : ℝ := γ k*((spectralNorm (W k)+f k)*
  baseEnvelope d N W X γ f k+f k*frobNorm (X k))

def matrixRemainderConstant : ℝ := remainderConstant
  (fun k => γ k*spectralNorm (W k)) (fun k => γ k*f k)
  (residualEnvelope d N W X γ f) L


theorem base_actual_linear_envelope (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hf : ∀ k < L, 0 ≤ f k) (hγ : ∀ k < L, 0 ≤ γ k)
    (hE : ∀ k < L, spectralNorm (E k) ≤ t*f k)
    (hinit : B 0=X 0)
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k))
    (hB : ∀ k < L, B (k+1)=σ k ((W k+E k)*B k))
    (hlip : ∀ k < L, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V)) :
    frobNorm (X L-B L) ≤ t*baseEnvelope d N W X γ f L := by
  unfold baseEnvelope
  rw [← weightedBound_smul]
  apply recurrence_bound (fun k => frobNorm (X k-B k)) _ _ L
  · simp [hinit,frobNorm]
  · intro k hk; exact mul_nonneg (hγ k hk) (add_nonneg (spectralNorm_nonneg _) (hf k hk))
  · intro k hk
    have he1 : spectralNorm (E k) ≤ f k := by nlinarith [hE k hk,hf k hk]
    have hres := base_residual_envelope (W k) (E k) (X k) (B k)
    have h1 := mul_le_mul_of_nonneg_right he1 (frobNorm_nonneg (X k-B k))
    have h2 := mul_le_mul_of_nonneg_right (hE k hk) (frobNorm_nonneg (X k))
    have hsum : frobNorm (W k*X k-(W k+E k)*B k) ≤
        (spectralNorm (W k)+f k)*frobNorm (X k-B k)+t*f k*frobNorm (X k) := by linarith
    have hout := hlip k hk (W k*X k) ((W k+E k)*B k)
    rw [← hX k hk,← hB k hk] at hout
    have hm := mul_le_mul_of_nonneg_left hsum (hγ k hk)
    nlinarith



theorem base_actual_residual_envelope (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hf : ∀ k < L, 0 ≤ f k) (hγ : ∀ k < L, 0 ≤ γ k)
    (hE : ∀ k < L, spectralNorm (E k) ≤ t*f k)
    (hinit : B 0=X 0)
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k))
    (hB : ∀ k < L, B (k+1)=σ k ((W k+E k)*B k))
    (hlip : ∀ k < L, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V)) :
    ∀ k < L, γ k*frobNorm (W k*X k-(W k+E k)*B k) ≤
      t*residualEnvelope d N W X γ f k := by
  intro k hk
  have hbase := base_actual_linear_envelope d N k W E X B γ f σ t ht0 ht1
    (fun j hj => hf j (by omega)) (fun j hj => hγ j (by omega))
    (fun j hj => hE j (by omega)) hinit (fun j hj => hX j (by omega))
    (fun j hj => hB j (by omega)) (fun j hj => hlip j (by omega))
  have he1 : spectralNorm (E k) ≤ f k := by nlinarith [hE k hk,hf k hk]
  have hres := base_residual_envelope (W k) (E k) (X k) (B k)
  have h1 := mul_le_mul_of_nonneg_right he1 (frobNorm_nonneg (X k-B k))
  have h2 := mul_le_mul_of_nonneg_right (hE k hk) (frobNorm_nonneg (X k))
  have h3 := mul_le_mul_of_nonneg_left hbase (add_nonneg (spectralNorm_nonneg (W k)) (hf k hk))
  have hs : frobNorm (W k*X k-(W k+E k)*B k) ≤
      t*((spectralNorm (W k)+f k)*baseEnvelope d N W X γ f k+f k*frobNorm (X k)) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (hγ k hk)
  dsimp [residualEnvelope]
  nlinarith



theorem matrix_actual_first_order_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hf : ∀ k < L, 0 ≤ f k) (hE : ∀ k < L, spectralNorm (E k) ≤ t*f k)
    (hinitB : B 0=X 0) (hinitQ : Q 0=X 0)
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k))
    (hQ : ∀ k < L, Q (k+1)=σ k ((correctedWeight (W k) (X k) (Q k) (α k)+E k)*Q k))
    (hB : ∀ k < L, B (k+1)=σ k ((W k+E k)*B k))
    (hgram : ∀ k < L, IsUnit (gram (Q k)).det)
    (hα : ∀ k < L, 0 ≤ α k ∧ α k ≤ 1) (hγ : ∀ k < L, 0 ≤ γ k)
    (hlip : ∀ k < L, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V)) :
    frobNorm (X L-Q L) ≤ weightedBound (fun k => γ k*spectralNorm (W k))
      (fun k => γ k*frobNorm (W k*X k-(W k+E k)*B k)) L +
      t^2*matrixRemainderConstant d N L W X γ f := by
  have hmain := matrix_actual_composite d N L W E X B Q α γ σ hinitB hinitQ hX hQ hB hgram hα hγ hlip
  have hres := base_actual_residual_envelope d N L W E X B γ f σ t ht0 ht1 hf hγ hE hinitB hX hB hlip
  have hdiff := weightedBound_diff_quadratic
    (fun k => γ k*spectralNorm (W k))
    (fun k => γ k*(spectralNorm (W k)+spectralNorm (E k))) (fun k => γ k*f k)
    (fun k => γ k*frobNorm (W k*X k-(W k+E k)*B k))
    (residualEnvelope d N W X γ f) L t ht0 ht1
  have h0 : ∀ k < L, 0 ≤ γ k*spectralNorm (W k) := fun k hk => mul_nonneg (hγ k hk) (spectralNorm_nonneg _)
  have hf0 : ∀ k < L, 0 ≤ γ k*f k := fun k hk => mul_nonneg (hγ k hk) (hf k hk)
  have hc0 : ∀ k < L, 0 ≤ γ k*frobNorm (W k*X k-(W k+E k)*B k) :=
    fun k hk => mul_nonneg (hγ k hk) (frobNorm_nonneg _)
  have hEnv : ∀ k < L, 0 ≤ residualEnvelope d N W X γ f k := by
    intro k hk
    have hb := weightedBound_nonneg
      (fun j => γ j*(spectralNorm (W j)+f j)) (fun j => γ j*f j*frobNorm (X j)) k
      (fun j hj => mul_nonneg (hγ j (by omega)) (add_nonneg (spectralNorm_nonneg _) (hf j (by omega))))
      (fun j hj => mul_nonneg (mul_nonneg (hγ j (by omega)) (hf j (by omega))) (frobNorm_nonneg _))
    exact mul_nonneg (hγ k hk) (add_nonneg
      (mul_nonneg (add_nonneg (spectralNorm_nonneg _) (hf k hk)) hb)
      (mul_nonneg (hf k hk) (frobNorm_nonneg _)))
  have ha : ∀ k < L, γ k*spectralNorm (W k) ≤ γ k*(spectralNorm (W k)+spectralNorm (E k)) ∧
      γ k*(spectralNorm (W k)+spectralNorm (E k)) ≤ γ k*spectralNorm (W k)+t*(γ k*f k) := by
    intro k hk
    have hn := mul_nonneg (hγ k hk) (spectralNorm_nonneg (E k))
    have hm := mul_le_mul_of_nonneg_left (hE k hk) (hγ k hk)
    constructor <;> nlinarith
  have hh := (hdiff h0 hf0 hc0 hEnv ha hres).2
  dsimp [matrixRemainderConstant]
  linarith

end
end QepV1
