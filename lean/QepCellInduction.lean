import QepLinearInduction
import QepCellProjection





set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QepLinear
noncomputable section
open Matrix QepCorrected

variable {d e m κ : Type*} [Fintype d] [Fintype e] [Fintype m] [Fintype κ]
  [DecidableEq d] [DecidableEq e] [DecidableEq m]


theorem T11_error_congr_cell (α : ℝ) (Z X : Mat d m) (P J : Mat m m) (F : Mat e d)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z)
    (hJs : Jᵀ = J) (hJ : J * J = J) (hc : P * J = J * P) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Loewner (F * ((Tmix α Z X P * J - X * J) * (Tmix α Z X P * J - X * J)ᵀ) * Fᵀ)
      (F * ((Z * J - X * J) * (Z * J - X * J)ᵀ) * Fᵀ) := by
  rw [T7_Tmix_cell α Z X P J hJ hc]
  exact T8_error_congr α (Z * J) (X * J) (J * P * J) F (T7_cell_symm P J hs hJs)
    (T7_cell_idem P J hp hJ hc) (T7_cell_fix Z P J hz hJ hc) h0 h1


theorem T11_gram_congr_cell (α : ℝ) (Z X : Mat d m) (P J : Mat m m) (F : Mat e d)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z)
    (hJs : Jᵀ = J) (hJ : J * J = J) (hc : P * J = J * P) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Loewner (F * ((Tmix α Z X P * J) * (Tmix α Z X P * J)ᵀ) * Fᵀ)
      (F * ((1 - α) • ((Z * J) * (Z * J)ᵀ) + α • ((X * J) * (X * J)ᵀ)) * Fᵀ) := by
  rw [T7_Tmix_cell α Z X P J hJ hc]
  exact T8_gram_congr α (Z * J) (X * J) (J * P * J) F (T7_cell_symm P J hs hJs)
    (T7_cell_idem P J hp hJ hc) (T7_cell_fix Z P J hz hJ hc) h0 h1


theorem T11_error_congr_cell_mask (α : ℝ) (Z X : Mat d m) (P J : Mat m m)
    (W : Mat e d) (Dm : Mat e e)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z)
    (hJs : Jᵀ = J) (hJ : J * J = J) (hc : P * J = J * P) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Loewner
      (Dm * W * ((Tmix α Z X P * J - X * J) * (Tmix α Z X P * J - X * J)ᵀ) * (Dm * W)ᵀ)
      (Dm * W * ((Z * J - X * J) * (Z * J - X * J)ᵀ) * (Dm * W)ᵀ) :=
  T11_error_congr_cell α Z X P J (Dm * W) hs hp hz hJs hJ hc h0 h1


theorem T11_monotone_congr {f : Type*} [Fintype f] [DecidableEq f]
    (Ψ : Mat d d → Mat e e) (Dm : Mat f e)
    (hΨ : ∀ A B : Mat d d, Loewner A B → Loewner (Ψ A) (Ψ B)) :
    ∀ A B : Mat d d, Loewner A B → Loewner (Dm * Ψ A * Dmᵀ) (Dm * Ψ B * Dmᵀ) :=
  fun A B h => Loewner.congr (hΨ A B h) Dm


theorem T12_fSq_sum_cells (M : Mat d m) (J : κ → Mat m m)
    (hJs : ∀ c, (J c)ᵀ = J c) (hJ : ∀ c, J c * J c = J c) (hsum : ∑ c, J c = 1) :
    ∑ c, fSq (M * J c) = fSq M := by
  have h : ∀ c, fSq (M * J c) = Matrix.trace (M * J c * Mᵀ) := fun c => by
    rw [← trace_mul_transpose_eq_fSq, ← sandwich_eq_gram M (J c) (hJs c) (hJ c)]
  simp only [h]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum, Matrix.mul_one,
    trace_mul_transpose_eq_fSq]

end
end QepLinear
