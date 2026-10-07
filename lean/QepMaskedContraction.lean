import Mathlib





set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace QepMaskedContraction
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]


def nsq (v : n → ℝ) : ℝ := v ⬝ᵥ v

theorem nsq_eq_sum (v : n → ℝ) : nsq v = ∑ i, (v i)^2 := by
  simp [nsq, dotProduct, pow_two]

theorem nsq_nonneg (v : n → ℝ) : 0 ≤ nsq v := by
  rw [nsq_eq_sum]; exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem nsq_eq_zero {v : n → ℝ} (h : nsq v = 0) : v = 0 :=
  dotProduct_self_eq_zero.mp h

theorem nsq_vecMul (v : n → ℝ) (M : Matrix n n ℝ) :
    nsq (v ᵥ* M) = v ⬝ᵥ ((M * Mᵀ) *ᵥ v) := by
  unfold nsq
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]


theorem nsq_one_sub_smul_proj (P : Matrix n n ℝ) (hPt : Pᵀ = P) (hPP : P * P = P)
    (α : ℝ) (v : n → ℝ) :
    nsq (v ᵥ* (1 - α • P)) = nsq v - α * (2 - α) * nsq (v ᵥ* P) := by
  have hM : (1 - α • P) * (1 - α • P)ᵀ = 1 - (α * (2 - α)) • (P * Pᵀ) := by
    rw [transpose_sub, transpose_one, transpose_smul, hPt, hPP]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP]
    module
  rw [nsq_vecMul, hM, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, ← nsq_vecMul, smul_eq_mul]
  rfl

theorem masked_contraction_iff (P D : Matrix n n ℝ)
    (hPt : Pᵀ = P) (hPP : P * P = P) (hDt : Dᵀ = D) (hDD : D * D = D)
    {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1) :
    (∀ a : n → ℝ, nsq (a ᵥ* ((1 - α • P) * D)) ≤ nsq (a ᵥ* D)) ↔ P * D = D * P := by
  constructor
  · intro h
    have e1 : (1 - D) * D = 0 := by rw [sub_mul, one_mul, hDD, sub_self]
    have e2 : (1 - D) * ((1 - α • P) * D) = (-α) • ((1 - D) * P * D) := by
      rw [sub_mul (1 : Matrix n n ℝ) (α • P) D, mul_sub, one_mul, e1, zero_sub,
        smul_mul_assoc, mul_smul_comm, neg_smul, Matrix.mul_assoc]
    have key : (1 - D) * P * D = 0 := by
      have h2 : ∀ b : n → ℝ, b ᵥ* ((1 - D) * P * D) = 0 := by
        intro b
        have hb := h (b ᵥ* (1 - D))
        rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, e1, e2] at hb
        have hz : nsq (b ᵥ* ((-α) • ((1 - D) * P * D)))
            = α^2 * nsq (b ᵥ* ((1 - D) * P * D)) := by
          rw [Matrix.vecMul_smul]
          simp only [nsq, dotProduct_smul, smul_dotProduct, smul_eq_mul]
          ring
        have hzero : nsq (b ᵥ* (0 : Matrix n n ℝ)) = 0 := by simp [nsq]
        rw [hz, hzero] at hb
        have hpos : 0 < α^2 := by positivity
        have hn := nsq_nonneg (b ᵥ* ((1 - D) * P * D))
        apply nsq_eq_zero
        nlinarith
      ext i j
      have := congrFun (h2 (Pi.single i 1)) j
      simpa using this
    have hPD : P * D = D * P * D := by
      have := key
      rw [sub_mul, sub_mul, one_mul, sub_eq_zero] at this
      exact this
    have hDP : D * P = D * P * D := by
      have := congrArg transpose hPD
      simp only [transpose_mul, hPt, hDt] at this
      exact this.trans (Matrix.mul_assoc _ _ _).symm
    exact hPD.trans hDP.symm
  · intro hc a
    have hcomm : (1 - α • P) * D = D * (1 - α • P) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hc]
    rw [hcomm, ← Matrix.vecMul_vecMul, nsq_one_sub_smul_proj P hPt hPP]
    have hn := nsq_nonneg ((a ᵥ* D) ᵥ* P)
    have : 0 ≤ α * (2 - α) * nsq ((a ᵥ* D) ᵥ* P) :=
      mul_nonneg (mul_nonneg h0.le (by linarith)) hn
    linarith


theorem masked_contraction_iff_diagonal (P : Matrix n n ℝ) (d : n → ℝ)
    (hPt : Pᵀ = P) (hPP : P * P = P) (hd : ∀ i, d i = 0 ∨ d i = 1)
    {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1) :
    (∀ a : n → ℝ, nsq (a ᵥ* ((1 - α • P) * diagonal d)) ≤ nsq (a ᵥ* diagonal d))
      ↔ P * diagonal d = diagonal d * P := by
  apply masked_contraction_iff P (diagonal d) hPt hPP (diagonal_transpose d) _ h0 h1
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]

end QepMaskedContraction
