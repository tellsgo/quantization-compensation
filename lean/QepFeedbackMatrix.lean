import QepFeedbackCovariance
import QepFeedbackFiniteEnergy
import Mathlib.MeasureTheory.Integral.Pi
set_option maxHeartbeats 2000000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra
open QepFeedbackMoments QepFeedbackEnergy QepFeedbackConditionalMoments QepFeedbackLDL
open QepFeedbackCovariance QepFeedbackFiniteEnergy
namespace QepFeedbackMatrix
noncomputable section

def matrixNoise (m n : ℕ) : Measure (Fin m → History n) := Measure.pi (fun _ => historyNoise n)
def actualMatrix (mode : ℕ → Option ℕ) (origin step : ℕ → ℝ) {m : ℕ}
    (weight : Fin m → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (n : ℕ) (p : Fin m → History n) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => errors mode origin step (weight i) U n (p i) j

def frobSq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, (M i j)^2

theorem actualMatrix_row (mode : ℕ → Option ℕ) (origin step : ℕ → ℝ) {m : ℕ}
    (weight : Fin m → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (n d : ℕ)
    (Z : Matrix (Fin n) (Fin d) ℝ) (p : Fin m → History n) (i : Fin m) (k : Fin d) :
    (actualMatrix mode origin step weight U n p*Z) i k =
    (errorRow mode origin step (weight i) U n (p i)*Z) () k := rfl


theorem actual_matrix_innovations_joint_law (mode : ℕ → Option ℕ) (origin step : ℕ → ℝ)
    {m : ℕ} (weight : Fin m → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (n : ℕ) :
    MeasurePreserving (fun p : Fin m → History n => fun i =>
      causalInnovations mode (normalizedTarget mode origin step (weight i) U) n (p i))
      (matrixNoise m n) (matrixNoise m n) := by
  exact measurePreserving_pi _ _ (fun i =>
    causal_innovations_measurePreserving _ _ (normalizedTarget_measurable _ _ _ _ _) n)

theorem actual_matrix_unbounded_energy (origin step : ℕ → ℝ) {m : ℕ}
    (weight : Fin m → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0)
    (hstep : ∀ n,step n≠0) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) :
    (∫ p, frobSq (actualMatrix (fun _ => none) origin step weight U n p*Z) ∂matrixNoise m n)=
      (m:ℝ)*(∑ k : Fin d,∑ j : Fin n,(step j.val)^2/12*(((triangle U n)⁻¹*Z) j k)^2) := by
  have hi (i : Fin m) : Integrable (fun p => rowSq
      (errorRow (fun _ => none) origin step (weight i) U n p*Z)) (historyNoise n) := by
    exact integrable_finsetSum _ (fun k _ => actual_output_square_integrable origin step (weight i) U hU hstep n d Z k)
  have hip (i : Fin m) : Integrable (fun p : Fin m → History n => rowSq
      (errorRow (fun _ => none) origin step (weight i) U n (p i)*Z)) (Measure.pi (fun _ : Fin m => historyNoise n)) :=
    (measurePreserving_eval (fun _ : Fin m => historyNoise n) i).integrable_comp_of_integrable (hi i)
  change (∫ p, ∑ i : Fin m,rowSq (errorRow (fun _ => none) origin step (weight i) U n (p i)*Z)
    ∂Measure.pi (fun _ : Fin m => historyNoise n)) = _
  rw [integral_finsetSum Finset.univ (fun i _ => hip i)]
  have he (i : Fin m) : (∫ p : Fin m → History n,rowSq
      (errorRow (fun _ => none) origin step (weight i) U n (p i)*Z) ∂Measure.pi (fun _ : Fin m => historyNoise n)) =
      ∑ k : Fin d,∑ j : Fin n,(step j.val)^2/12*(((triangle U n)⁻¹*Z) j k)^2 :=
    (integral_comp_eval (μ:=fun _ : Fin m => historyNoise n) (i:=i) (hi i).aestronglyMeasurable).trans
      (actual_output_energy origin step (weight i) U hU hstep n d Z)
  simp_rw [he]
  simp


theorem actual_matrix_finite_energy (codes : ℕ → ℕ) (origin step : ℕ → ℝ) {m : ℕ}
    (weight : Fin m → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0)
    (pivot : ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose) :
    (∫ p, frobSq (actualMatrix (fun i => some (codes i)) origin step weight U n p*Z) ∂matrixNoise m n)=
      (m:ℝ)*(∑ j : Fin n,pivot j.val*(step j.val)^2/12)+
      (∫ p, ∑ i : Fin m,weightedOverload (fun i => some (codes i)) origin step (weight i) U pivot n (p i) ∂matrixNoise m n) := by
  have hd (i : Fin m) := weightedDrive_integrable codes origin step (weight i) U pivot n
  have ho (i : Fin m) := weightedOverload_integrable codes origin step (weight i) U pivot n
  have hdp (i : Fin m) : Integrable (fun p : Fin m → History n =>
      weightedDrive (fun i => some (codes i)) origin step (weight i) U pivot n (p i))
      (Measure.pi (fun _ : Fin m => historyNoise n)) :=
    (measurePreserving_eval (fun _ : Fin m => historyNoise n) i).integrable_comp_of_integrable (hd i)
  have hop (i : Fin m) : Integrable (fun p : Fin m → History n =>
      weightedOverload (fun i => some (codes i)) origin step (weight i) U pivot n (p i))
      (Measure.pi (fun _ : Fin m => historyNoise n)) :=
    (measurePreserving_eval (fun _ : Fin m => historyNoise n) i).integrable_comp_of_integrable (ho i)
  change (∫ p, ∑ i : Fin m,rowSq (errorRow (fun i => some (codes i)) origin step (weight i) U n (p i)*Z)
    ∂Measure.pi (fun _ : Fin m => historyNoise n)) = _
  simp_rw [actual_matched_energy _ origin step _ U hU pivot n d Z hgram]
  rw [integral_finsetSum Finset.univ (fun i _ => hdp i)]
  change _ = _+(∫ p, ∑ i : Fin m,weightedOverload _ origin step (weight i) U pivot n (p i)
    ∂Measure.pi (fun _ : Fin m => historyNoise n))
  rw [integral_finsetSum Finset.univ (fun i _ => hop i)]
  have he (i : Fin m) : (∫ p : Fin m → History n,weightedDrive (fun i => some (codes i))
      origin step (weight i) U pivot n (p i) ∂Measure.pi (fun _ : Fin m => historyNoise n)) =
      (∑ j : Fin n,pivot j.val*(step j.val)^2/12)+
      (∫ p : Fin m → History n,weightedOverload (fun i => some (codes i))
      origin step (weight i) U pivot n (p i) ∂Measure.pi (fun _ : Fin m => historyNoise n)) := by
    rw [integral_comp_eval (μ:=fun _ : Fin m => historyNoise n) (i:=i) (hd i).aestronglyMeasurable,integral_comp_eval (μ:=fun _ : Fin m => historyNoise n) (i:=i) (ho i).aestronglyMeasurable]
    exact finite_weighted_energy codes origin step (weight i) U pivot n
  simp_rw [he]
  simp [Finset.sum_add_distrib]

end
end QepFeedbackMatrix
