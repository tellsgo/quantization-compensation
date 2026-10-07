import QepFeedbackAlgebra
set_option maxHeartbeats 1600000
open QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra
namespace QepFeedbackLDL
noncomputable section

def rowSq {n : ℕ} (E : Row n) : ℝ := ∑ j, (E () j)^2

theorem row_gram_entry {n : ℕ} (E : Row n) : (E*E.transpose) () () = rowSq E := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,rowSq,pow_two]


theorem row_energy_of_factor {n d : ℕ} (E V : Row n) (Z : Matrix (Fin n) (Fin d) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (pivot : Fin n → ℝ)
    (hgram : Z*Z.transpose=T*Matrix.diagonal pivot*T.transpose) (hEV : E*T=V) :
    rowSq (E*Z) = ∑ j, pivot j*(V () j)^2 := by
  have hm : (E*Z)*(E*Z).transpose = V*Matrix.diagonal pivot*V.transpose := by
    calc
      _ = E*(Z*Z.transpose)*E.transpose := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = (E*T)*Matrix.diagonal pivot*(E*T).transpose := by rw [hgram]; simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hEV]
  rw [← row_gram_entry (E*Z),hm]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

def weightedDrive (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (pivot : ℕ → ℝ) (n : ℕ) (p : History n) : ℝ :=
  ∑ j : Fin n, pivot j.val*(driving mode origin step weight U n p j)^2

def weightedOverload (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (pivot : ℕ → ℝ) (n : ℕ) (p : History n) : ℝ :=
  ∑ j : Fin n, pivot j.val*(overloadVector mode origin step weight U n p j)^2

theorem actual_matched_energy (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j, j ≤ i → U i j=0) (pivot : ℕ → ℝ)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose)
    (p : History n) :
    rowSq (errorRow mode origin step weight U n p * Z) = weightedDrive mode origin step weight U pivot n p := by
  exact row_energy_of_factor _ _ Z (triangle U n) _ hgram
    (actual_error_mul_triangle mode origin step weight U hU n p)

theorem weightedDrive_succ (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (pivot : ℕ → ℝ) (n : ℕ) (p : History (n+1)) :
    weightedDrive mode origin step weight U pivot (n+1) p =
      weightedDrive mode origin step weight U pivot n p.1 + pivot n*
        (overload mode origin step weight U n p.1+freshInnovation mode origin step weight U n p)^2 := by
  simp only [weightedDrive,Fin.sum_univ_castSucc,driving,Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last]
  ring

theorem weightedOverload_succ (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (pivot : ℕ → ℝ) (n : ℕ) (p : History (n+1)) :
    weightedOverload mode origin step weight U pivot (n+1) p =
      weightedOverload mode origin step weight U pivot n p.1 + pivot n*(overload mode origin step weight U n p.1)^2 := by
  simp only [weightedOverload,Fin.sum_univ_castSucc,overloadVector,Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last]

end
end QepFeedbackLDL
