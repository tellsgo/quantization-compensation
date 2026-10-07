import QepCorrected





set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QepLinear
noncomputable section
open Matrix QepCorrected

variable {d m : Type*} [Fintype d] [Fintype m] [DecidableEq m] [DecidableEq d]


def Tmix (α : ℝ) (Z X : Mat d m) (P : Mat m m) : Mat d m :=
  (1 - α) • Z + α • (X * P)


theorem T1_residual_factor (α : ℝ) (Z X : Mat d m) (P : Mat m m) (hz : Z * P = Z) :
    Tmix α Z X P - X = (Z - X) * (1 - α • P) := by
  unfold Tmix
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, hz]
  module


theorem one_sub_smul_proj_sq (α : ℝ) (P : Mat m m) (hs : Pᵀ = P) (hp : P * P = P) :
    (1 - α • P) * (1 - α • P)ᵀ = 1 - (α * (2 - α)) • P := by
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hs,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, hp]
  module


theorem T2_first_identity (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) :
    (Z - X) * (Z - X)ᵀ - (Tmix α Z X P - X) * (Tmix α Z X P - X)ᵀ =
      (α * (2 - α)) • ((Z - X) * P * (Z - X)ᵀ) := by
  rw [T1_residual_factor α Z X P hz]
  generalize Z - X = D
  have h : D * (1 - α • P) * (D * (1 - α • P))ᵀ =
      D * ((1 - α • P) * (1 - α • P)ᵀ) * Dᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [h, one_sub_smul_proj_sq α P hs hp]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  module


theorem T3_second_identity (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) :
    (1 - α) • (Z * Zᵀ) + α • (X * Xᵀ) - Tmix α Z X P * (Tmix α Z X P)ᵀ =
      α • (X * (1 - P) * Xᵀ) + (α * (1 - α)) • ((Z - X * P) * (Z - X * P)ᵀ) := by
  have hz' : P * Zᵀ = Zᵀ := by
    have := congrArg Matrix.transpose hz
    rwa [Matrix.transpose_mul, hs] at this
  have hzM : ∀ M : Mat m d, Z * (P * M) = Z * M := fun M => by
    rw [← Matrix.mul_assoc, hz]
  have hpM : ∀ M : Mat m d, P * (P * M) = P * M := fun M => by
    rw [← Matrix.mul_assoc, hp]
  unfold Tmix
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, hs, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_one,
    hzM, hpM, hz', smul_add, smul_sub, smul_smul]
  module


theorem sandwich_eq_gram {k : Type*} [Fintype k] (A : Mat k m) (Q : Mat m m)
    (hs : Qᵀ = Q) (hp : Q * Q = Q) : A * Q * Aᵀ = (A * Q) * (A * Q)ᵀ := by
  rw [Matrix.transpose_mul, hs, Matrix.mul_assoc A Q (Q * Aᵀ), ← Matrix.mul_assoc Q Q, hp,
    Matrix.mul_assoc]

theorem gram_posSemidef {k : Type*} [Fintype k] (A : Mat k m) : (A * Aᵀ).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this


theorem T4_first_rhs_posSemidef (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (h0 : 0 ≤ α) (h2 : α ≤ 2) :
    ((α * (2 - α)) • ((Z - X) * P * (Z - X)ᵀ)).PosSemidef := by
  rw [sandwich_eq_gram (Z - X) P hs hp]
  exact (gram_posSemidef _).smul (mul_nonneg h0 (by linarith))


theorem T4_second_rhs_posSemidef (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (α • (X * (1 - P) * Xᵀ) +
      (α * (1 - α)) • ((Z - X * P) * (Z - X * P)ᵀ)).PosSemidef := by
  have hs' : (1 - P)ᵀ = 1 - P := by rw [Matrix.transpose_sub, Matrix.transpose_one, hs]
  have hp' : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hp]
    abel
  rw [sandwich_eq_gram X (1 - P) hs' hp']
  exact ((gram_posSemidef _).smul h0).add
    ((gram_posSemidef _).smul (mul_nonneg h0 (by linarith)))


theorem T4_first_loewner (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) (h0 : 0 ≤ α) (h2 : α ≤ 2) :
    ((Z - X) * (Z - X)ᵀ - (Tmix α Z X P - X) * (Tmix α Z X P - X)ᵀ).PosSemidef := by
  rw [T2_first_identity α Z X P hs hp hz]
  exact T4_first_rhs_posSemidef α Z X P hs hp h0 h2


theorem T4_second_loewner (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ((1 - α) • (Z * Zᵀ) + α • (X * Xᵀ) - Tmix α Z X P * (Tmix α Z X P)ᵀ).PosSemidef := by
  rw [T3_second_identity α Z X P hs hp hz]
  exact T4_second_rhs_posSemidef α Z X P hs hp h0 h1


theorem trace_mul_transpose_eq_fSq (M : Mat d m) : Matrix.trace (M * Mᵀ) = fSq M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, fSq,
    pow_two]


theorem T5_trace (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Matrix.trace (Tmix α Z X P * (Tmix α Z X P)ᵀ) ≤
      (1 - α) * Matrix.trace (Z * Zᵀ) + α * Matrix.trace (X * Xᵀ) := by
  have h := (T4_second_loewner α Z X P hs hp hz h0 h1).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul] at h
  simp only [smul_eq_mul] at h
  linarith


theorem T5_frobenius (α : ℝ) (Z X : Mat d m) (P : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    fSq (Tmix α Z X P) ≤ (1 - α) * fSq Z + α * fSq X := by
  have h := T5_trace α Z X P hs hp hz h0 h1
  simpa only [trace_mul_transpose_eq_fSq] using h

end
end QepLinear
