import QepLinearIdentities





set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QepLinear
noncomputable section
open Matrix QepCorrected

variable {d m : Type*} [Fintype d] [Fintype m] [DecidableEq m] [DecidableEq d]


theorem diagonal_zero_one_proj (c : m → ℝ) (hc : ∀ i, c i = 0 ∨ c i = 1) :
    (Matrix.diagonal c : Mat m m)ᵀ = Matrix.diagonal c ∧
      (Matrix.diagonal c : Mat m m) * Matrix.diagonal c = Matrix.diagonal c := by
  refine ⟨Matrix.diagonal_transpose c, ?_⟩
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases hc i with h | h <;> simp [h]

theorem T7_cell_symm (P J : Mat m m) (hs : Pᵀ = P) (hJs : Jᵀ = J) :
    (J * P * J)ᵀ = J * P * J := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hs, hJs, Matrix.mul_assoc]

theorem T7_cell_idem (P J : Mat m m) (hp : P * P = P) (hJ : J * J = J)
    (hc : P * J = J * P) : (J * P * J) * (J * P * J) = J * P * J := by
  calc (J * P * J) * (J * P * J) = J * P * (J * J) * P * J := by
        simp only [Matrix.mul_assoc]
    _ = J * (P * J) * P * J := by rw [hJ]; simp only [Matrix.mul_assoc]
    _ = J * (J * P) * P * J := by rw [hc]
    _ = (J * J) * (P * P) * J := by simp only [Matrix.mul_assoc]
    _ = J * P * J := by rw [hJ, hp]

theorem T7_cell_fix (Z : Mat d m) (P J : Mat m m) (hz : Z * P = Z) (hJ : J * J = J)
    (hc : P * J = J * P) : (Z * J) * (J * P * J) = Z * J := by
  calc (Z * J) * (J * P * J) = Z * (J * J) * P * J := by simp only [Matrix.mul_assoc]
    _ = Z * (J * P) * J := by rw [hJ]; simp only [Matrix.mul_assoc]
    _ = Z * (P * J) * J := by rw [hc]
    _ = (Z * P) * (J * J) := by simp only [Matrix.mul_assoc]
    _ = Z * J := by rw [hz, hJ]

theorem T7_cell_target (X : Mat d m) (P J : Mat m m) (hJ : J * J = J)
    (hc : P * J = J * P) : X * P * J = (X * J) * (J * P * J) := by
  symm
  calc (X * J) * (J * P * J) = X * (J * J) * P * J := by simp only [Matrix.mul_assoc]
    _ = X * (J * P) * J := by rw [hJ]; simp only [Matrix.mul_assoc]
    _ = X * (P * J) * J := by rw [hc]
    _ = X * P * (J * J) := by simp only [Matrix.mul_assoc]
    _ = X * P * J := by rw [hJ]


theorem T7_Tmix_cell (α : ℝ) (Z X : Mat d m) (P J : Mat m m) (hJ : J * J = J)
    (hc : P * J = J * P) :
    Tmix α Z X P * J = Tmix α (Z * J) (X * J) (J * P * J) := by
  unfold Tmix
  rw [← T7_cell_target X P J hJ hc, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul]


theorem T7_T1_cell (α : ℝ) (Z X : Mat d m) (P J : Mat m m)
    (hz : Z * P = Z) (hJ : J * J = J) (hc : P * J = J * P) :
    Tmix α Z X P * J - X * J = (Z * J - X * J) * (1 - α • (J * P * J)) := by
  rw [T7_Tmix_cell α Z X P J hJ hc]
  exact T1_residual_factor α (Z * J) (X * J) (J * P * J) (T7_cell_fix Z P J hz hJ hc)


theorem T7_T2_cell (α : ℝ) (Z X : Mat d m) (P J : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z)
    (hJs : Jᵀ = J) (hJ : J * J = J) (hc : P * J = J * P) :
    (Z * J - X * J) * (Z * J - X * J)ᵀ -
        (Tmix α Z X P * J - X * J) * (Tmix α Z X P * J - X * J)ᵀ =
      (α * (2 - α)) • ((Z * J - X * J) * (J * P * J) * (Z * J - X * J)ᵀ) := by
  rw [T7_Tmix_cell α Z X P J hJ hc]
  exact T2_first_identity α (Z * J) (X * J) (J * P * J) (T7_cell_symm P J hs hJs)
    (T7_cell_idem P J hp hJ hc) (T7_cell_fix Z P J hz hJ hc)


theorem T7_T3_cell (α : ℝ) (Z X : Mat d m) (P J : Mat m m)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z)
    (hJs : Jᵀ = J) (hJ : J * J = J) (hc : P * J = J * P) :
    (1 - α) • ((Z * J) * (Z * J)ᵀ) + α • ((X * J) * (X * J)ᵀ) -
        (Tmix α Z X P * J) * (Tmix α Z X P * J)ᵀ =
      α • ((X * J) * (1 - J * P * J) * (X * J)ᵀ) +
        (α * (1 - α)) •
          ((Z * J - X * J * (J * P * J)) * (Z * J - X * J * (J * P * J))ᵀ) := by
  rw [T7_Tmix_cell α Z X P J hJ hc]
  exact T3_second_identity α (Z * J) (X * J) (J * P * J) (T7_cell_symm P J hs hJs)
    (T7_cell_idem P J hp hJ hc) (T7_cell_fix Z P J hz hJ hc)

end
end QepLinear
