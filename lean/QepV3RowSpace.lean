import QepGram

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV3
noncomputable section
open QepCorrected QepGram
variable {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]


theorem row_factor_projection (X Z : Mat n t) (D : Mat n n)
    (hZ : IsUnit (gram Z).det) (hXZ : X=D*Z) : X*gramProjection Z=X := by
  rw [hXZ,Matrix.mul_assoc,input_times_projection Z hZ]


theorem gram_left_invertible (A : Mat n n) (Z : Mat n t)
    (hA : IsUnit A.det) (hZ : IsUnit (gram Z).det) : IsUnit (gram (A*Z)).det := by
  have he : gram (A*Z)=A*gram Z*A.transpose := by
    simp [gram,Matrix.transpose_mul,Matrix.mul_assoc]
  rw [he,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  exact (hA.mul hZ).mul hA


theorem row_factor_next (W A D : Mat n n) (X Z : Mat n t)
    (hA : IsUnit A.det) (hXZ : X=D*Z) :
    W*X=(W*D*A⁻¹)*(A*Z) := by
  rw [hXZ]
  have he : (W*D*A⁻¹)*(A*Z)=(W*D)*(A⁻¹*A)*Z := by simp [Matrix.mul_assoc]
  rw [he,Matrix.nonsing_inv_mul _ hA,Matrix.mul_one,Matrix.mul_assoc]



theorem equal_width_row_condition (W A : ℕ → Mat n n) (X Z : ℕ → Mat n t) (L : ℕ)
    (hinit : Z 0=X 0) (hrow : LinearIndependent ℝ (X 0).row)
    (hX : ∀ k < L, X (k+1)=W k*X k)
    (hZ : ∀ k < L, Z (k+1)=A k*Z k)
    (hA : ∀ k < L, IsUnit (A k).det) :
    ∀ k ≤ L, IsUnit (gram (Z k)).det ∧ X k*gramProjection (Z k)=X k := by
  have hmain : ∀ k ≤ L, IsUnit (gram (Z k)).det ∧ ∃ D : Mat n n, X k=D*Z k := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_,1,?_⟩
      · rw [hinit]; exact gram_isUnit_det_of_full_row_rank _ hrow
      · simp [hinit]
    | succ k ih =>
      obtain ⟨hg,D,hD⟩ := ih (by omega)
      refine ⟨?_,W k*D*(A k)⁻¹,?_⟩
      · rw [hZ k (by omega)]
        exact gram_left_invertible (A k) (Z k) (hA k (by omega)) hg
      · rw [hX k (by omega),hZ k (by omega)]
        exact row_factor_next _ _ _ _ _ (hA k (by omega)) hD
  intro k hk
  obtain ⟨hg,D,hD⟩ := hmain k hk
  exact ⟨hg,row_factor_projection _ _ D hg hD⟩


theorem actual_error_step_unreduced (W E : Mat m n) (X Z : Mat n t) (a : ℝ) :
    (correctedWeight W X Z a+E)*Z-W*X =
      W*(Z-X)-a • (W*(Z-X)*gramProjection Z)+E*Z := by
  simp only [correctedWeight,Matrix.add_mul,Matrix.smul_mul,correction_times_input,
    Matrix.mul_sub,Matrix.sub_mul,smul_sub]
  abel



theorem actual_error_step (W E : Mat m n) (X Z : Mat n t) (a : ℝ)
    (hZ : IsUnit (gram Z).det) (hrow : X*gramProjection Z=X) :
    (correctedWeight W X Z a+E)*Z-W*X = (1-a) • (W*(Z-X))+E*Z := by
  have hr : (Z-X)*gramProjection Z=Z-X := by
    rw [Matrix.sub_mul,input_times_projection Z hZ,hrow]
  rw [actual_error_step_unreduced,Matrix.mul_assoc,hr]
  rw [sub_smul,one_smul]

end
end QepV3
