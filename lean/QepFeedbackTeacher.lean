import QepFeedbackLoss
set_option maxHeartbeats 1600000
open MeasureTheory Matrix
open QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra QepFeedbackLDL QepFeedbackLoss
namespace QepFeedbackTeacher
noncomputable section

def weightRow (weight : ℕ → ℝ) (n : ℕ) : Row n := fun _ j => weight j.val

def reconstructionRow (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) : Row n :=
  weightRow weight n+errorRow (fun i => some (codes i)) origin step weight U n p

def teacherLoss (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (Y : Row d) : ℝ :=
  ∫ p,rowSq (Y-reconstructionRow codes origin step weight U n p*Z) ∂historyNoise n

theorem actual_teacher_loss_bridge (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (Y : Row d) :
    teacherLoss codes origin step weight U n d Z Y =
    actualLoss codes origin step weight U n d Z (Y-weightRow weight n*Z) := by
  unfold teacherLoss actualLoss reconstructionRow
  simp only [Matrix.add_mul,sub_add_eq_sub_sub]

theorem affine_target_residual (weight direction : ℕ → ℝ) (alpha : ℝ)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (Y : Row d) :
    Y-weightRow (fun i => weight i+alpha*direction i) n*Z=
      (Y-weightRow weight n*Z)-alpha • (weightRow direction n*Z) := by
  have hw : weightRow (fun i => weight i+alpha*direction i) n=
      weightRow weight n+alpha • weightRow direction n := by ext i j; rfl
  rw [hw,Matrix.add_mul,Matrix.smul_mul,sub_add_eq_sub_sub]


theorem actual_teacher_loss_difference (codes : ℕ → ℕ) (origin step weight direction : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0) (pivot : ℕ → ℝ)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose)
    (Y : Row d) (alpha : ℝ)
    (hproj : rowInner (Y-weightRow weight n*Z) (weightRow direction n*Z)=rowSq (weightRow direction n*Z)) :
    teacherLoss codes origin step (fun i => weight i+alpha*direction i) U n d Z Y-
      teacherLoss codes origin step weight U n d Z Y =
    -alpha*(2-alpha)*rowSq (weightRow direction n*Z)-
      2*rowInner ((Y-weightRow weight n*Z)-alpha • (weightRow direction n*Z))
        (meanOverloadOutput codes origin step (fun i => weight i+alpha*direction i) U n d Z)+
      2*rowInner (Y-weightRow weight n*Z) (meanOverloadOutput codes origin step weight U n d Z)+
      (∫ p,weightedOverload (fun i => some (codes i)) origin step (fun i => weight i+alpha*direction i) U pivot n p ∂historyNoise n)-
      (∫ p,weightedOverload (fun i => some (codes i)) origin step weight U pivot n p ∂historyNoise n) := by
  rw [actual_teacher_loss_bridge,actual_teacher_loss_bridge,affine_target_residual]
  exact actual_loss_difference codes origin step weight (fun i => weight i+alpha*direction i) U hU pivot n d Z hgram
    _ _ alpha hproj

end
end QepFeedbackTeacher
