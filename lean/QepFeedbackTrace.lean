import QepFeedbackMatrix
set_option maxHeartbeats 2000000
open MeasureTheory
open QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra QepFeedbackEnergy
open QepFeedbackCovariance QepFeedbackLDL QepFeedbackMatrix
namespace QepFeedbackTrace
noncomputable section

def variance (step : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (step i.val)^2/12)


theorem actual_error_covariance (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hU : ∀ i j,j ≤ i → U i j=0) (hstep : ∀ n,step n≠0) (n : ℕ) :
    (fun j k : Fin n => ∫ p,errorRow (fun _ => none) origin step weight U n p () j*
      errorRow (fun _ => none) origin step weight U n p () k ∂historyNoise n) =
    ((triangle U n)⁻¹).transpose*variance step n*(triangle U n)⁻¹ := by
  ext j k
  have hc := actual_output_cross origin step weight U hU hstep n n (1 : Matrix (Fin n) (Fin n) ℝ) j k
  simp only [Matrix.mul_one] at hc
  rw [hc,Matrix.mul_apply]
  simp only [variance,Matrix.mul_diagonal,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem trace_sum {n d : ℕ} (step : ℕ → ℝ) (M : Matrix (Fin n) (Fin d) ℝ) :
    Matrix.trace (variance step n*M*M.transpose)=
      ∑ k : Fin d,∑ j : Fin n,(step j.val)^2/12*(M j k)^2 := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  conv_lhs => arg 2; intro i; rw [Matrix.mul_apply]
  simp only [variance,Matrix.diagonal_mul,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _; apply Finset.sum_congr rfl
  intro j _; ring


theorem actual_matrix_trace_energy (origin step : ℕ → ℝ) {m : ℕ}
    (weight : Fin m → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0)
    (hstep : ∀ n,step n≠0) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) :
    (∫ p,frobSq (actualMatrix (fun _ => none) origin step weight U n p*Z) ∂matrixNoise m n)=
      (m:ℝ)*Matrix.trace (variance step n*(triangle U n)⁻¹*(Z*Z.transpose)*((triangle U n)⁻¹).transpose) := by
  rw [actual_matrix_unbounded_energy origin step weight U hU hstep]
  have heq : variance step n*(triangle U n)⁻¹*(Z*Z.transpose)*((triangle U n)⁻¹).transpose=
      variance step n*((triangle U n)⁻¹*Z)*((triangle U n)⁻¹*Z).transpose := by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  rw [heq,trace_sum]


theorem filtered_matched_gram (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0)
    (pivot : ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose) :
    (triangle U n)⁻¹*(Z*Z.transpose)*((triangle U n)⁻¹).transpose =
      Matrix.diagonal (fun j : Fin n => pivot j.val) := by
  have hr : (triangle U n)⁻¹*triangle U n=1 := Matrix.nonsing_inv_mul _ (by rw [triangle_det U hU]; norm_num)
  have ht : (triangle U n).transpose*((triangle U n)⁻¹).transpose=1 := by
    rw [← Matrix.transpose_mul,hr,Matrix.transpose_one]
  calc
    _ = ((triangle U n)⁻¹*triangle U n)*Matrix.diagonal (fun j : Fin n => pivot j.val)*
      ((triangle U n).transpose*((triangle U n)⁻¹).transpose) := by rw [hgram]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hr,ht,Matrix.one_mul,Matrix.mul_one]

theorem actual_matrix_matched_unbounded_energy (origin step : ℕ → ℝ) {m : ℕ}
    (weight : Fin m → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0)
    (hstep : ∀ n,step n≠0) (pivot : ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose) :
    (∫ p,frobSq (actualMatrix (fun _ => none) origin step weight U n p*Z) ∂matrixNoise m n)=
      (m:ℝ)*(∑ j : Fin n,(step j.val)^2/12*pivot j.val) := by
  rw [actual_matrix_trace_energy origin step weight U hU hstep]
  have hm : variance step n*(triangle U n)⁻¹*(Z*Z.transpose)*((triangle U n)⁻¹).transpose =
    variance step n*((triangle U n)⁻¹*(Z*Z.transpose)*((triangle U n)⁻¹).transpose) := by simp only [Matrix.mul_assoc]
  rw [hm,filtered_matched_gram U hU pivot n d Z hgram]
  simp only [variance,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal]

end
end QepFeedbackTrace
