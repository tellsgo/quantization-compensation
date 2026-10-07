import QepCorrected

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QepGram
noncomputable section
open scoped BigOperators
open QepCorrected

variable {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq n] [DecidableEq t]

def gram (Z : Mat n t) : Mat n n := Z * Z.transpose
def gramProjection (Z : Mat n t) : Mat t t := Z.transpose * (gram Z)⁻¹ * Z
def correction (W : Mat m n) (X Z : Mat n t) : Mat m n :=
  W * (X-Z) * Z.transpose * (gram Z)⁻¹
def correctedWeight (W : Mat m n) (X Z : Mat n t) (a : ℝ) : Mat m n :=
  W + a • correction W X Z


theorem gram_isUnit_det_of_full_row_rank (Z : Mat n t)
    (hrow : LinearIndependent ℝ Z.row) : IsUnit (gram Z).det := by
  have hpd : (Z * Z.conjTranspose).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self Z (Matrix.vecMul_injective_iff.mpr hrow)
  have hunit : IsUnit (gram Z) := by
    simpa [gram] using hpd.isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit

theorem gramProjection_symmetric (Z : Mat n t) :
    (gramProjection Z).transpose = gramProjection Z := by
  simp [gramProjection, gram, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.mul_assoc]

theorem input_times_projection (Z : Mat n t) (h : IsUnit (gram Z).det) :
    Z * gramProjection Z = Z := by
  calc
    _ = (gram Z * (gram Z)⁻¹) * Z := by
      simp only [gramProjection, gram, Matrix.mul_assoc]
    _ = Z := by rw [Matrix.mul_nonsing_inv _ h, Matrix.one_mul]

theorem gramProjection_idempotent (Z : Mat n t) (h : IsUnit (gram Z).det) :
    gramProjection Z * gramProjection Z = gramProjection Z := by
  change (Z.transpose * (gram Z)⁻¹ * Z) * gramProjection Z = _
  rw [Matrix.mul_assoc, input_times_projection Z h]
  rfl

theorem error_in_projection (E : Mat m n) (Z : Mat n t)
    (h : IsUnit (gram Z).det) :
    (E * Z) * gramProjection Z = E * Z := by
  rw [Matrix.mul_assoc, input_times_projection Z h]

theorem correction_times_input (W : Mat m n) (X Z : Mat n t) :
    correction W X Z * Z = (W * (X-Z)) * gramProjection Z := by
  simp only [correction, gramProjection, Matrix.mul_assoc]

theorem actual_residual_eq (W E : Mat m n) (X Z : Mat n t) (a : ℝ) :
    W*X - (correctedWeight W X Z a + E)*Z =
      residual (W*(X-Z)) (E*Z) (W*(X-Z)*gramProjection Z) a := by
  have h : W*X - (correctedWeight W X Z a + E)*Z =
      W*(X-Z) - E*Z - a • (correction W X Z * Z) := by
    simp only [correctedWeight, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul]
    abel
  rw [h, correction_times_input]
  ext i j
  simp [QepCorrected.residual, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]


theorem qep_improvement_iff (W E : Mat m n) (X Z : Mat n t)
    (h : IsUnit (gram Z).det) (a : ℝ) (ha : 0 < a) :
    fSq (W*X-(correctedWeight W X Z a+E)*Z) ≤ fSq (W*X-(W+E)*Z) ↔
      2*fInner (E*Z) (W*(X-Z)*gramProjection Z) ≤
        (2-a)*fSq (W*(X-Z)*gramProjection Z) := by
  have hbase := actual_residual_eq W E X Z 0
  simp only [correctedWeight, zero_smul, add_zero] at hbase
  rw [actual_residual_eq, hbase]
  exact improvement_iff _ _ _ (gramProjection_symmetric Z) (gramProjection_idempotent Z h) a ha

theorem fSq_sub (A B : Mat m t) :
    fSq (A-B) = fSq A + fSq B - 2*fInner A B := by
  have h : (∑ i, ∑ j, (A i j-B i j)^2) =
      ∑ i, ∑ j, ((A i j)^2+(B i j)^2-2*(A i j*B i j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [fSq, fInner, Matrix.sub_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum] using h

theorem orthogonal_split (A B : Mat m t) (P : Mat t t)
    (hs : P.transpose=P) (hp : P*P=P) (hb : B*P=B) :
    fSq (A-B) = fSq (A-A*P) + fSq (A*P-B) := by
  have hc : fInner A B = fInner (A*P) B := by
    have h := inner_right_mul A B P
    rwa [hb, hs] at h
  have h1 := fSq_sub A (A*P)
  have h2 := fSq_sub A B
  have h3 := fSq_sub (A*P) B
  rw [projection_inner A P hs hp] at h1
  rw [hc] at h2
  linarith


theorem orthogonal_decomposition (W Q : Mat m n) (X Z : Mat n t)
    (h : IsUnit (gram Z).det) :
    fSq (W*X-Q*Z) = fSq (W*(X-Z)*(1-gramProjection Z)) +
      fSq ((correctedWeight W X Z 1-Q)*Z) := by
  have he := orthogonal_split (W*(X-Z)) ((Q-W)*Z) (gramProjection Z)
    (gramProjection_symmetric Z) (gramProjection_idempotent Z h)
    (error_in_projection (Q-W) Z h)
  have ha : W*(X-Z)-(Q-W)*Z = W*X-Q*Z := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hb : W*(X-Z)-W*(X-Z)*gramProjection Z = W*(X-Z)*(1-gramProjection Z) := by
    simp only [Matrix.mul_sub, Matrix.mul_one]
  have hc : W*(X-Z)*gramProjection Z-(Q-W)*Z = (correctedWeight W X Z 1-Q)*Z := by
    rw [← correction_times_input]
    simp only [correctedWeight, one_smul, Matrix.sub_mul, Matrix.add_mul]
    abel
  simpa only [ha,hb,hc] using he

theorem qep_improvement_iff_of_full_row_rank (W E : Mat m n) (X Z : Mat n t)
    (hrow : LinearIndependent ℝ Z.row) (a : ℝ) (ha : 0<a) :
    fSq (W*X-(correctedWeight W X Z a+E)*Z) ≤ fSq (W*X-(W+E)*Z) ↔
      2*fInner (E*Z) (W*(X-Z)*gramProjection Z) ≤
        (2-a)*fSq (W*(X-Z)*gramProjection Z) :=
  qep_improvement_iff W E X Z (gram_isUnit_det_of_full_row_rank Z hrow) a ha

theorem orthogonal_decomposition_of_full_row_rank (W Q : Mat m n) (X Z : Mat n t)
    (hrow : LinearIndependent ℝ Z.row) :
    fSq (W*X-Q*Z) = fSq (W*(X-Z)*(1-gramProjection Z)) +
      fSq ((correctedWeight W X Z 1-Q)*Z) :=
  orthogonal_decomposition W Q X Z (gram_isUnit_det_of_full_row_rank Z hrow)

end
end QepGram
