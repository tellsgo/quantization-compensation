import Mathlib




set_option autoImplicit false
namespace QepReluAlgebra
noncomputable section

def relu (x : ℝ) : ℝ := max x 0

def corr (α W Xl Zl : ℝ) : ℝ := α * (W * (Xl - Zl) * Zl * (Zl * Zl)⁻¹)

def X : ℝ := 1
def W1 : ℝ := 1
def W2 : ℝ := -1/4

def X2 : ℝ := relu (W1 * X)
def Xout : ℝ := relu (W2 * X2)

def Q1 (α1 u : ℝ) : ℝ := W1 + corr α1 W1 X X + u
def Z2 (α1 u : ℝ) : ℝ := relu (Q1 α1 u * X)

def bQ2 (v : ℝ) : ℝ := W2 + v
def bOut (α1 u v : ℝ) : ℝ := relu (bQ2 v * Z2 α1 u)

def qTarget (α1 u : ℝ) : ℝ := W2 + corr 1 W2 X2 (Z2 α1 u)
def qQ2 (α1 u v : ℝ) : ℝ := qTarget α1 u + v
def qOut (α1 u v : ℝ) : ℝ := relu (qQ2 α1 u v * Z2 α1 u)

theorem teacher : X2 = 1 ∧ Xout = 0 := by
  constructor <;> norm_num [X2, Xout, relu, W1, W2, X]

theorem first_weight (α1 u : ℝ) : Q1 α1 u = 1 + u := by
  simp [Q1, corr, W1, X]

theorem second_input (α1 u : ℝ) (hz : 0 < 1 + u) : Z2 α1 u = 1 + u := by
  rw [Z2, first_weight, relu, X, mul_one, max_eq_left hz.le]

theorem qep_target (α1 u : ℝ) (hz : 0 < 1 + u) : qTarget α1 u = -1 / (4 * (1 + u)) := by
  rw [qTarget, second_input α1 u hz, teacher.1, corr, W2]
  have : (1 + u) ≠ 0 := hz.ne'
  field_simp
  ring

theorem base_output (α1 u v : ℝ) (hz : 0 < 1 + u) :
    bOut α1 u v = (1 + u) * max (v - 1/4) 0 := by
  rw [bOut, second_input α1 u hz, relu, bQ2, W2, mul_max_of_nonneg _ _ hz.le]
  congr 1 <;> ring

theorem qep_output (α1 u v : ℝ) (hz : 0 < 1 + u) :
    qOut α1 u v = max (v * (1 + u) - 1/4) 0 := by
  rw [qOut, qQ2, qep_target α1 u hz, second_input α1 u hz, relu]
  congr 1
  have : (1 + u) ≠ 0 := hz.ne'
  field_simp
  ring

theorem core (α1 u v : ℝ) (hz : 0 < 1 + u) :
    Z2 α1 u = 1 + u ∧ qTarget α1 u = -1 / (4 * (1 + u)) ∧
    bOut α1 u v = (1 + u) * max (v - 1/4) 0 ∧
    qOut α1 u v = max (v * (1 + u) - 1/4) 0 :=
  ⟨second_input α1 u hz, qep_target α1 u hz, base_output α1 u v hz, qep_output α1 u v hz⟩

end
end QepReluAlgebra
