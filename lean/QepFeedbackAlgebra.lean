import QepFeedbackProcess
set_option maxHeartbeats 1800000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess
namespace QepFeedbackAlgebra
noncomputable section


def driving (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) : (n : ℕ) → History n → Fin n → ℝ
  | 0 => fun _ i => Fin.elim0 i
  | n+1 => fun p => Fin.snoc (driving mode origin step weight U n p.1)
      (freshInnovation mode origin step weight U n p + overload mode origin step weight U n p.1)

def noiseVector (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) : (n : ℕ) → History n → Fin n → ℝ
  | 0 => fun _ i => Fin.elim0 i
  | n+1 => fun p => Fin.snoc (noiseVector mode origin step weight U n p.1)
      (freshInnovation mode origin step weight U n p)

def overloadVector (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) : (n : ℕ) → History n → Fin n → ℝ
  | 0 => fun _ i => Fin.elim0 i
  | n+1 => fun p => Fin.snoc (overloadVector mode origin step weight U n p.1)
      (overload mode origin step weight U n p.1)

theorem driving_split (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) (j : Fin n) :
    driving mode origin step weight U n p j =
      noiseVector mode origin step weight U n p j + overloadVector mode origin step weight U n p j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [driving,noiseVector,overloadVector]
    · simpa only [driving,noiseVector,overloadVector,Fin.snoc_castSucc] using ih p.1 i


theorem actual_triangular_identity (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j, j ≤ i → U i j = 0)
    (n : ℕ) (p : History n) (j : Fin n) :
    errors mode origin step weight U n p j +
      (∑ i : Fin n, errors mode origin step weight U n p i * U i.val j.val) =
      driving mode origin step weight U n p j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc, errors, Fin.snoc_last, Fin.snoc_castSucc,
        hU n n (le_refl n), mul_zero, add_zero, driving]
      simpa only [errors,Fin.snoc_last] using actual_column_identity mode origin step weight U n p
    · rw [Fin.sum_univ_castSucc]
      have hz : U n j.val = 0 := hU n j.val (Nat.le_of_lt j.isLt)
      simpa only [Fin.val_castSucc,Fin.val_last,errors,Fin.snoc_castSucc,hz,mul_zero,add_zero,
        driving] using ih p.1 j

abbrev Row (n : ℕ) := Matrix Unit (Fin n) ℝ
def errorRow (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) : Row n := fun _ => errors mode origin step weight U n p
def drivingRow (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) : Row n := fun _ => driving mode origin step weight U n p
def feedbackMatrix (U : ℕ → ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => U i.val j.val
def triangle (U : ℕ → ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := 1 + feedbackMatrix U n

theorem actual_error_mul_triangle (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j, j ≤ i → U i j = 0)
    (n : ℕ) (p : History n) :
    errorRow mode origin step weight U n p * triangle U n = drivingRow mode origin step weight U n p := by
  unfold triangle
  rw [Matrix.mul_add, Matrix.mul_one]
  ext i j
  exact actual_triangular_identity mode origin step weight U hU n p j

theorem triangle_det (U : ℕ → ℕ → ℝ) (hU : ∀ i j, j ≤ i → U i j = 0) (n : ℕ) :
    (triangle U n).det = 1 := by
  have ht : (triangle U n).IsUpperTriangular := by
    intro i j hij
    simp only [triangle,Matrix.add_apply,Matrix.one_apply,feedbackMatrix]
    have hn : i ≠ j := ne_of_gt hij
    simp [hn,hU i.val j.val (le_of_lt hij)]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [triangle,feedbackMatrix,hU]

theorem actual_error_inverse_filter (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j, j ≤ i → U i j = 0)
    (n : ℕ) (p : History n) :
    errorRow mode origin step weight U n p = drivingRow mode origin step weight U n p * (triangle U n)⁻¹ := by
  have hu : IsUnit (triangle U n).det := by rw [triangle_det U hU n]; exact isUnit_one
  rw [← actual_error_mul_triangle mode origin step weight U hU n p,Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu,Matrix.mul_one]

end
end QepFeedbackAlgebra
