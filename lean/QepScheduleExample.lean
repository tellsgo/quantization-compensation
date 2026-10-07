import Mathlib






set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
namespace QepScheduleExample
noncomputable section
open scoped Matrix
abbrev Mat (ι κ : Type*) := Matrix ι κ ℝ
def fSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Mat ι κ) : ℝ := ∑ i, ∑ j, (A i j)^2

def corr {μ ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (α : ℝ) (W : Mat μ ι) (Xl Zl : Mat ι κ) : Mat μ ι :=
  α • (W * (Xl - Zl) * Zlᵀ * (Zl * Zlᵀ)⁻¹)

def X : Mat (Fin 4) (Fin 4) := 1
def W1 : Mat (Fin 2) (Fin 4) := !![1,0,0,0;0,1,0,0]
def W2 : Mat (Fin 1) (Fin 2) := !![1,0]
def W3 : Mat (Fin 1) (Fin 1) := !![1]
def E1 (u1 u2 : ℝ) : Mat (Fin 2) (Fin 4) := !![0,0,u1,0;0,0,0,u2]
def E2 (η : ℝ) : Mat (Fin 1) (Fin 2) := !![0,η]
def E3 : Mat (Fin 1) (Fin 1) := 0

def X2 : Mat (Fin 2) (Fin 4) := W1 * X
def X3 : Mat (Fin 1) (Fin 4) := W2 * X2
def X4 : Mat (Fin 1) (Fin 4) := W3 * X3

def Q1 (α1 u1 u2 : ℝ) : Mat (Fin 2) (Fin 4) := W1 + corr α1 W1 X X + E1 u1 u2
def Z2 (α1 u1 u2 : ℝ) : Mat (Fin 2) (Fin 4) := Q1 α1 u1 u2 * X
def Q2 (α1 u1 u2 η a : ℝ) : Mat (Fin 1) (Fin 2) :=
  W2 + corr a W2 X2 (Z2 α1 u1 u2) + E2 η
def Z3 (α1 u1 u2 η a : ℝ) : Mat (Fin 1) (Fin 4) := Q2 α1 u1 u2 η a * Z2 α1 u1 u2
def Q3 (α1 u1 u2 η a : ℝ) : Mat (Fin 1) (Fin 1) :=
  W3 + corr 1 W3 X3 (Z3 α1 u1 u2 η a) + E3
def Z4 (α1 u1 u2 η a : ℝ) : Mat (Fin 1) (Fin 4) := Q3 α1 u1 u2 η a * Z3 α1 u1 u2 η a

def L (α1 u1 u2 η a : ℝ) : ℝ := fSq (X4 - Z4 α1 u1 u2 η a)

def bQ1 (u1 u2 : ℝ) : Mat (Fin 2) (Fin 4) := W1 + E1 u1 u2
def bZ2 (u1 u2 : ℝ) : Mat (Fin 2) (Fin 4) := bQ1 u1 u2 * X
def bQ2 (η : ℝ) : Mat (Fin 1) (Fin 2) := W2 + E2 η
def bZ3 (u1 u2 η : ℝ) : Mat (Fin 1) (Fin 4) := bQ2 η * bZ2 u1 u2
def bQ3 : Mat (Fin 1) (Fin 1) := W3 + E3
def bZ4 (u1 u2 η : ℝ) : Mat (Fin 1) (Fin 4) := bQ3 * bZ3 u1 u2 η
def Lbase (u1 u2 η : ℝ) : ℝ := fSq (X4 - bZ4 u1 u2 η)


def kk (u1 a : ℝ) : ℝ := 1 - a * u1^2 / (1 + u1^2)

def GG (u1 u2 η a : ℝ) : ℝ := (1 + u1^2) * (kk u1 a)^2 + (1 + u2^2) * η^2

def Q1e (u1 u2 : ℝ) : Mat (Fin 2) (Fin 4) := !![1,0,u1,0;0,1,0,u2]
def Z3e (k u1 u2 η : ℝ) : Mat (Fin 1) (Fin 4) := !![k, η, k*u1, η*u2]

theorem teacher : X2 = W1 ∧ X3 = !![1,0,0,0] ∧ X4 = !![1,0,0,0] := by
  have h2 : X2 = W1 := by simp [X2, X]
  have h3 : X3 = !![1,0,0,0] := by
    rw [X3, h2]
    ext i j; fin_cases i; fin_cases j <;>
      simp [W1, W2, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨h2, h3, ?_⟩
  rw [X4, h3]
  ext i j; fin_cases i; fin_cases j <;>
    simp [W3, Matrix.mul_apply, Fin.sum_univ_succ]


theorem Q1_eq (α1 u1 u2 : ℝ) : Q1 α1 u1 u2 = Q1e u1 u2 ∧ Z2 α1 u1 u2 = Q1e u1 u2 := by
  have h : Q1 α1 u1 u2 = Q1e u1 u2 := by
    simp only [Q1, corr, sub_self, Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero]
    ext i j; fin_cases i <;> fin_cases j <;> simp [W1, E1, Q1e]
  exact ⟨h, by rw [Z2, h, X, Matrix.mul_one]⟩

theorem gram2_eq (u1 u2 : ℝ) :
    Q1e u1 u2 * (Q1e u1 u2)ᵀ = !![1 + u1^2, 0; 0, 1 + u2^2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Q1e, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;> ring

theorem gram2_inverse_certificate (u1 u2 : ℝ) :
    Q1e u1 u2 * (Q1e u1 u2)ᵀ * !![1/(1 + u1^2), 0; 0, 1/(1 + u2^2)] = 1 := by
  have hA : (1 + u1^2) ≠ 0 := by positivity
  have hB : (1 + u2^2) ≠ 0 := by positivity
  rw [gram2_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hA, hB]

theorem gram2_unit (α1 u1 u2 : ℝ) : IsUnit (Z2 α1 u1 u2 * (Z2 α1 u1 u2)ᵀ).det := by
  rw [(Q1_eq α1 u1 u2).2]
  exact Matrix.isUnit_det_of_right_inverse (gram2_inverse_certificate u1 u2)

theorem Q2_eq (α1 u1 u2 η a : ℝ) : Q2 α1 u1 u2 η a = !![kk u1 a, η] := by
  have hA : (1 + u1^2) ≠ 0 := by positivity
  have hd : W1 - Q1e u1 u2 = !![0,0,-u1,0;0,0,0,-u2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [W1, Q1e]
  have h1 : W2 * (!![0,0,-u1,0;0,0,0,-u2] : Mat (Fin 2) (Fin 4)) = !![0,0,-u1,0] := by
    ext i j; fin_cases i; fin_cases j <;> simp [W2, Matrix.mul_apply, Fin.sum_univ_succ]
  have h2 : (!![0,0,-u1,0] : Mat (Fin 1) (Fin 4)) * (Q1e u1 u2)ᵀ = !![-u1^2, 0] := by
    ext i j; fin_cases i; fin_cases j <;>
      simp [Q1e, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;> ring
  have h3 : (!![-u1^2, 0] : Mat (Fin 1) (Fin 2)) * !![1/(1 + u1^2), 0; 0, 1/(1 + u2^2)]
      = !![-u1^2/(1 + u1^2), 0] := by
    ext i j; fin_cases i; fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  rw [Q2, corr, (Q1_eq α1 u1 u2).2, teacher.1,
    Matrix.inv_eq_right_inv (gram2_inverse_certificate u1 u2), hd, h1, h2, h3]
  ext i j; fin_cases i; fin_cases j <;> simp [W2, E2, kk] <;> ring

theorem Z3_eq (α1 u1 u2 η a : ℝ) : Z3 α1 u1 u2 η a = Z3e (kk u1 a) u1 u2 η := by
  rw [Z3, Q2_eq, (Q1_eq α1 u1 u2).2]
  ext i j; fin_cases i; fin_cases j <;>
    simp [Q1e, Z3e, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gram3_eq (k u1 u2 η : ℝ) :
    Z3e k u1 u2 η * (Z3e k u1 u2 η)ᵀ = !![(1 + u1^2) * k^2 + (1 + u2^2) * η^2] := by
  ext i j; fin_cases i; fin_cases j
  simp [Z3e, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  ring

theorem gram3_inverse_certificate (k u1 u2 η : ℝ)
    (hG : (1 + u1^2) * k^2 + (1 + u2^2) * η^2 ≠ 0) :
    Z3e k u1 u2 η * (Z3e k u1 u2 η)ᵀ * !![1/((1 + u1^2) * k^2 + (1 + u2^2) * η^2)] = 1 := by
  rw [gram3_eq]
  ext i j; fin_cases i; fin_cases j
  simp [Matrix.mul_apply, hG]

theorem Q3_eq (α1 u1 u2 η a : ℝ) (hG : GG u1 u2 η a ≠ 0) :
    Q3 α1 u1 u2 η a = !![kk u1 a / GG u1 u2 η a] := by
  have hG' : (1 + u1^2) * (kk u1 a)^2 + (1 + u2^2) * η^2 ≠ 0 := hG
  have h1 : (X3 - Z3e (kk u1 a) u1 u2 η) * (Z3e (kk u1 a) u1 u2 η)ᵀ
      = !![kk u1 a - GG u1 u2 η a] := by
    have hx : (!![1,0,0,0] : Mat (Fin 1) (Fin 4)) * (Z3e (kk u1 a) u1 u2 η)ᵀ = !![kk u1 a] := by
      ext i j; fin_cases i; fin_cases j
      simp [Z3e, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
        Matrix.vecMul, dotProduct]
    rw [Matrix.sub_mul, gram3_eq, teacher.2.1, hx]
    ext i j; fin_cases i; fin_cases j
    simp [GG]
  rw [Q3, corr, Z3_eq, Matrix.inv_eq_right_inv (gram3_inverse_certificate _ u1 u2 η hG'),
    Matrix.mul_assoc W3, h1]
  ext i j; fin_cases i; fin_cases j
  simp [W3, E3, Matrix.mul_apply]
  change 1 + (kk u1 a - GG u1 u2 η a) * (GG u1 u2 η a)⁻¹ = kk u1 a / GG u1 u2 η a
  field_simp
  ring

theorem Z4_eq (α1 u1 u2 η a : ℝ) (hG : GG u1 u2 η a ≠ 0) :
    Z4 α1 u1 u2 η a = (kk u1 a / GG u1 u2 η a) • Z3e (kk u1 a) u1 u2 η := by
  rw [Z4, Q3_eq α1 u1 u2 η a hG, Z3_eq]
  ext i j; fin_cases i; fin_cases j <;> simp [Z3e, Matrix.mul_apply]


theorem L_closed (α1 u1 u2 η a : ℝ) (hG : GG u1 u2 η a ≠ 0) :
    L α1 u1 u2 η a = 1 - (kk u1 a)^2 / GG u1 u2 η a := by
  rw [L, Z4_eq α1 u1 u2 η a hG, teacher.2.2]
  have hG' : (1 + u1^2) * (kk u1 a)^2 + (1 + u2^2) * η^2 = GG u1 u2 η a := rfl
  generalize hk : kk u1 a = k at *
  generalize hg : GG u1 u2 η a = G at *
  simp [fSq, Z3e, Fin.sum_univ_succ]
  field_simp
  rw [← hG']
  ring

theorem Lbase_closed (u1 u2 η : ℝ) : Lbase u1 u2 η = η^2 + u1^2 + η^2 * u2^2 := by
  have hZ2 : bZ2 u1 u2 = Q1e u1 u2 := by
    rw [bZ2, X, Matrix.mul_one, bQ1]
    ext i j; fin_cases i <;> fin_cases j <;> simp [W1, E1, Q1e]
  have hQ2 : bQ2 η = !![1, η] := by
    ext i j; fin_cases i; fin_cases j <;> simp [bQ2, W2, E2]
  have hZ3 : bZ3 u1 u2 η = !![1, η, u1, η*u2] := by
    rw [bZ3, hZ2, hQ2]
    ext i j; fin_cases i; fin_cases j <;>
      simp [Q1e, Matrix.mul_apply, Fin.sum_univ_succ]
  have hZ4 : bZ4 u1 u2 η = !![1, η, u1, η*u2] := by
    rw [bZ4, hZ3, bQ3, E3, add_zero]
    ext i j; fin_cases i; fin_cases j <;> simp [W3, Matrix.mul_apply]
  rw [Lbase, hZ4, teacher.2.2]
  simp [fSq, Fin.sum_univ_succ]
  ring


theorem L_values (α1 u1 u2 η : ℝ) (h1 : u1^2 = 1) (h2 : u2^2 = 1) (hη : η^2 = 1/4) :
    L α1 u1 u2 η (1/2) = 17/26 ∧ L α1 u1 u2 η 1 = 3/4 ∧ Lbase u1 u2 η = 3/2 := by
  have hk1 : kk u1 (1/2) = 3/4 := by rw [kk, h1]; norm_num
  have hk2 : kk u1 1 = 1/2 := by rw [kk, h1]; norm_num
  have hg1 : GG u1 u2 η (1/2) = 13/8 := by rw [GG, hk1, h1, h2, hη]; norm_num
  have hg2 : GG u1 u2 η 1 = 1 := by rw [GG, hk2, h1, h2, hη]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [L_closed _ _ _ _ _ (by rw [hg1]; norm_num), hk1, hg1]; norm_num
  · rw [L_closed _ _ _ _ _ (by rw [hg2]; norm_num), hk2, hg2]; norm_num
  · rw [Lbase_closed, h1, h2, hη]; norm_num

def sgn (i : Fin 2) : ℝ := if i = 0 then 1 else -1

theorem sgn_sq (i : Fin 2) : (sgn i)^2 = 1 := by fin_cases i <;> simp [sgn]


theorem averages (α1 : ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2, L α1 (sgn i) (sgn j) (sgn l / 2) (1/2)) / 8 = 17/26 ∧
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2, L α1 (sgn i) (sgn j) (sgn l / 2) 1) / 8 = 3/4 ∧
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2, Lbase (sgn i) (sgn j) (sgn l / 2)) / 8 = 3/2 := by
  have h : ∀ i j l : Fin 2,
      L α1 (sgn i) (sgn j) (sgn l / 2) (1/2) = 17/26 ∧ L α1 (sgn i) (sgn j) (sgn l / 2) 1 = 3/4 ∧
      Lbase (sgn i) (sgn j) (sgn l / 2) = 3/2 := fun i j l =>
    L_values α1 _ _ _ (sgn_sq i) (sgn_sq j) (by rw [div_pow, sgn_sq]; norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp only [(h _ _ _).1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  · simp only [(h _ _ _).2.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  · simp only [(h _ _ _).2.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num

end
end QepScheduleExample
