import Mathlib





set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
namespace QepNoncommutative
noncomputable section
open scoped Matrix
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
def fSq (A : M2) : ℝ := ∑ i, ∑ j, (A i j)^2
def fro (A : M2) : ℝ := Real.sqrt (fSq A)

def corr (α : ℝ) (W Xl Zl : M2) : M2 := α • (W * (Xl - Zl) * Zlᵀ * (Zl * Zlᵀ)⁻¹)

def N : M2 := !![0,1;0,0]
def D (a b : ℝ) : M2 := !![a,0;0,b]
def X : M2 := 1
def W1 : M2 := 1
def W2 (a b : ℝ) : M2 := D a b
def E1 (t : ℝ) : M2 := t • N
def E2 (a b t : ℝ) : M2 := t • (N * D a b - D a b * N)

def X2 : M2 := W1 * X
def X3 (a b : ℝ) : M2 := W2 a b * X2

def bQ1 (t : ℝ) : M2 := W1 + E1 t
def bZ2 (t : ℝ) : M2 := bQ1 t * X
def bQ2 (a b t : ℝ) : M2 := W2 a b + E2 a b t
def bZ3 (a b t : ℝ) : M2 := bQ2 a b t * bZ2 t
def bR1 (t : ℝ) : M2 := W1 * X - bQ1 t * X
def bR2 (a b t : ℝ) : M2 := W2 a b * X2 - bQ2 a b t * bZ2 t

def qQ1 (t : ℝ) : M2 := W1 + corr 1 W1 X X + E1 t
def qZ2 (t : ℝ) : M2 := qQ1 t * X
def qQ2 (a b t : ℝ) : M2 := W2 a b + corr 1 (W2 a b) X2 (qZ2 t) + E2 a b t
def qZ3 (a b t : ℝ) : M2 := qQ2 a b t * qZ2 t
def qR1 (t : ℝ) : M2 := W1 * X - qQ1 t * X
def qR2 (a b t : ℝ) : M2 := W2 a b * X2 - qQ2 a b t * qZ2 t


def bU (a b t : ℝ) : ℝ := a * fro (bR1 t) + fro (bR2 a b t)
def qU (a b t : ℝ) : ℝ := a * fro (qR1 t) + fro (qR2 a b t)

theorem D_eq_diagonal (a b : ℝ) : D a b = Matrix.diagonal ![a,b] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D]

theorem N_sq : N * N = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_succ]

theorem commutator (a b : ℝ) : N * D a b - D a b * N = (b - a) • N := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [N, D, Matrix.mul_apply, Fin.sum_univ_succ]

theorem noncommuting {a b : ℝ} (hab : a ≠ b) : N * D a b ≠ D a b * N := by
  intro h
  have hh := congrArg (fun M : M2 => M 0 1) h
  simp [N, D, Matrix.mul_apply, Fin.sum_univ_succ] at hh
  exact hab hh.symm

theorem X2_eq : X2 = 1 := by simp [X2, W1, X]
theorem X3_eq (a b : ℝ) : X3 a b = D a b := by simp [X3, W2, X2_eq]

theorem qQ1_eq (t : ℝ) : qQ1 t = 1 + t • N := by simp [qQ1, corr, W1, E1]
theorem bQ1_eq (t : ℝ) : bQ1 t = 1 + t • N := by simp [bQ1, W1, E1]


theorem second_input (t : ℝ) : bZ2 t = 1 + t • N ∧ qZ2 t = 1 + t • N := by
  simp [bZ2, qZ2, qQ1_eq, bQ1_eq, X]

theorem second_input_inverse (t : ℝ) :
    (1 + t • N) * (1 - t • N) = 1 ∧ (1 - t • N) * (1 + t • N) = 1 ∧
    (1 + t • N)⁻¹ = 1 - t • N := by
  have h1 : (1 + t • N) * (1 - t • N) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [N, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply]
  have h2 : (1 - t • N) * (1 + t • N) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [N, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply]
  exact ⟨h1, h2, Matrix.inv_eq_right_inv h1⟩

theorem Z2_explicit (t : ℝ) : (1 : M2) + t • N = !![1,t;0,1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [N, Matrix.one_apply]

theorem gram2_inverse_certificate (t : ℝ) :
    (!![1,t;0,1] : M2) * (!![1,t;0,1] : M2)ᵀ * !![1,-t;-t,1+t^2] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply] <;> ring

theorem gram2_unit (t : ℝ) : IsUnit ((qZ2 t) * (qZ2 t)ᵀ).det := by
  rw [(second_input t).2, Z2_explicit]
  exact Matrix.isUnit_det_of_right_inverse (gram2_inverse_certificate t)


theorem pinv_eq (t : ℝ) : (qZ2 t)ᵀ * ((qZ2 t) * (qZ2 t)ᵀ)⁻¹ = 1 - t • N := by
  rw [(second_input t).2, Z2_explicit, Matrix.inv_eq_right_inv (gram2_inverse_certificate t)]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply] <;> ring

theorem second_weights (a b t : ℝ) :
    bQ2 a b t = D a b + ((b - a) * t) • N ∧ qQ2 a b t = D a b + ((b - 2*a) * t) • N := by
  constructor
  · rw [bQ2, E2, commutator, W2, smul_smul, mul_comm]
  · have hc : D a b * (1 - (1 + t • N)) * (1 - t • N) = (-(a * t)) • N := by
      have h1 : (1 : M2) - (1 + t • N) = !![0,-t;0,0] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [N]
      have h2 : (1 : M2) - t • N = !![1,-t;0,1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [N]
      rw [h1, h2]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [N, D, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [qQ2, corr, Matrix.mul_assoc _ (qZ2 t)ᵀ, pinv_eq, (second_input t).2, X2_eq, E2,
      commutator, W2, hc, one_smul, smul_smul, add_assoc, ← add_smul]
    congr 2; ring

theorem outputs (a b t : ℝ) :
    bZ3 a b t = D a b + (b * t) • N ∧ qZ3 a b t = D a b + ((b - a) * t) • N := by
  constructor
  · rw [bZ3, (second_weights a b t).1, (second_input t).1]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [N, D, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply] <;> ring
  · rw [qZ3, (second_weights a b t).2, (second_input t).2]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [N, D, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.vecMul, dotProduct,
        Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply] <;> ring

theorem fSq_smul_N (c : ℝ) : fSq (c • N) = c^2 := by
  simp [fSq, N, Fin.sum_univ_succ]

theorem fSq_neg (A : M2) : fSq (-A) = fSq A := by simp [fSq]

theorem output_errors (a b t : ℝ) :
    fSq (X3 a b - bZ3 a b t) = b^2 * t^2 ∧ fSq (X3 a b - qZ3 a b t) = (a - b)^2 * t^2 := by
  rw [X3_eq, (outputs a b t).1, (outputs a b t).2, sub_add_cancel_left, sub_add_cancel_left,
    fSq_neg, fSq_neg, fSq_smul_N, fSq_smul_N]
  constructor <;> ring

theorem qep_strictly_worse {a b t : ℝ} (hb : 0 < b) (hab : 2*b < a) (ht : 0 < t) :
    fSq (X3 a b - bZ3 a b t) < fSq (X3 a b - qZ3 a b t) := by
  rw [(output_errors a b t).1, (output_errors a b t).2]
  have ht2 : 0 < t^2 := by positivity
  have : b^2 < (a - b)^2 := by nlinarith
  exact mul_lt_mul_of_pos_right this ht2

theorem residuals (a b t : ℝ) :
    bR1 t = (-t) • N ∧ qR1 t = (-t) • N ∧
    bR2 a b t = (-(b * t)) • N ∧ qR2 a b t = ((a - b) * t) • N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bR1, bQ1_eq]; simp [W1, X]
  · rw [qR1, qQ1_eq]; simp [W1, X]
  · have h := (outputs a b t).1
    rw [bZ3] at h
    rw [bR2, h, X2_eq, W2, Matrix.mul_one, sub_add_cancel_left, neg_smul]
  · have h := (outputs a b t).2
    rw [qZ3] at h
    rw [qR2, h, X2_eq, W2, Matrix.mul_one, sub_add_cancel_left, ← neg_smul]
    congr 1; ring

theorem fro_smul_N (c : ℝ) : fro (c • N) = |c| := by
  rw [fro, fSq_smul_N, Real.sqrt_sq_eq_abs]

theorem residual_norms {a b t : ℝ} (hb : 0 < b) (hab : 2*b < a) (ht : 0 < t) :
    fro (bR1 t) = t ∧ fro (qR1 t) = t ∧
    fro (bR2 a b t) = b * t ∧ fro (qR2 a b t) = (a - b) * t := by
  obtain ⟨h1, h2, h3, h4⟩ := residuals a b t
  rw [h1, h2, h3, h4, fro_smul_N, fro_smul_N, fro_smul_N, abs_neg, abs_neg,
    abs_of_pos ht, abs_of_pos (mul_pos hb ht), abs_of_pos (mul_pos (by linarith) ht)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem bounds {a b t : ℝ} (hb : 0 < b) (hab : 2*b < a) (ht : 0 < t) :
    bU a b t = a * t + b * t ∧ qU a b t = a * t + (a - b) * t ∧ bU a b t < qU a b t := by
  obtain ⟨h1, h2, h3, h4⟩ := residual_norms hb hab ht
  rw [bU, qU, h1, h2, h3, h4]
  refine ⟨rfl, rfl, ?_⟩
  nlinarith




theorem D_opnorm_certificate {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    (∀ v : Fin 2 → ℝ, (D a b).mulVec v ⬝ᵥ (D a b).mulVec v ≤ a^2 * (v ⬝ᵥ v)) ∧
    (D a b).mulVec ![1,0] ⬝ᵥ (D a b).mulVec ![1,0] = a^2 * (![1,0] ⬝ᵥ ![1,0]) := by
  constructor
  · intro v
    simp only [D, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
      Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons]
    have : b^2 ≤ a^2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 this) (sq_nonneg (v 1))]
  · simp [D, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring

theorem core {a b t : ℝ} (hb : 0 < b) (hab : 2*b < a) (ht : 0 < t) :
    N * N = 0 ∧ N * D a b - D a b * N = (b - a) • N ∧
    bZ2 t = 1 + t • N ∧ qZ2 t = 1 + t • N ∧ (1 + t • N)⁻¹ = 1 - t • N ∧
    bQ2 a b t = D a b + ((b - a) * t) • N ∧ qQ2 a b t = D a b + ((b - 2*a) * t) • N ∧
    bZ3 a b t = D a b + (b * t) • N ∧ qZ3 a b t = D a b + ((b - a) * t) • N ∧
    fSq (X3 a b - bZ3 a b t) = b^2 * t^2 ∧ fSq (X3 a b - qZ3 a b t) = (a - b)^2 * t^2 ∧
    fSq (X3 a b - bZ3 a b t) < fSq (X3 a b - qZ3 a b t) :=
  ⟨N_sq, commutator a b, (second_input t).1, (second_input t).2, (second_input_inverse t).2.2,
    (second_weights a b t).1, (second_weights a b t).2, (outputs a b t).1, (outputs a b t).2,
    (output_errors a b t).1, (output_errors a b t).2, qep_strictly_worse hb hab ht⟩

end
end QepNoncommutative
