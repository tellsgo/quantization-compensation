import QepFeedbackBias
set_option maxHeartbeats 2400000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackAlgebra
open QepFeedbackMoments QepFeedbackEnergy QepFeedbackFiniteL2 QepFeedbackFiniteEnergy
open QepFeedbackCovariance QepFeedbackConditionalMoments QepFeedbackLDL QepFeedbackBias
namespace QepFeedbackLoss
noncomputable section

def rowInner {d : ℕ} (A B : Row d) : ℝ := ∑ k,A () k*B () k

def meanOverloadOutput (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) : Row d :=
  fun _ k => ∫ p,(overloadRow (fun i => some (codes i)) origin step weight U n p*((triangle U n)⁻¹*Z)) () k ∂historyNoise n

def actualLoss (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (B : Row d) : ℝ :=
  ∫ p,rowSq (B-errorRow (fun i => some (codes i)) origin step weight U n p*Z) ∂historyNoise n

theorem rowSq_sub {d : ℕ} (A B : Row d) : rowSq (A-B)=rowSq A-2*rowInner A B+rowSq B := by
  unfold rowSq rowInner
  simp only [Matrix.sub_apply]
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _; ring

theorem finite_output_memLp (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ) (k : Fin d) :
    MemLp (fun p => (errorRow (fun i => some (codes i)) origin step weight U n p*Z) () k) 2 (historyNoise n) := by
  simp only [Matrix.mul_apply,errorRow]
  exact memLp_finsetSum _ (fun j _ => (finite_errors_memLp codes origin step weight U n j).mul_const _)


theorem actual_loss_formula (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0) (pivot : ℕ → ℝ)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose)
    (B : Row d) : actualLoss codes origin step weight U n d Z B =
    rowSq B-2*rowInner B (meanOverloadOutput codes origin step weight U n d Z)+
      (∑ j : Fin n,pivot j.val*(step j.val)^2/12)+
      (∫ p,weightedOverload (fun i => some (codes i)) origin step weight U pivot n p ∂historyNoise n) := by
  have hq (k : Fin d) := finite_output_memLp codes origin step weight U n d Z k
  have hc : Integrable (fun p => rowInner B (errorRow (fun i => some (codes i)) origin step weight U n p*Z)) (historyNoise n) :=
    integrable_finsetSum _ (fun k _ => (MemLp.integrable (by norm_num) (hq k)).const_mul _)
  have hs : Integrable (fun p => rowSq (errorRow (fun i => some (codes i)) origin step weight U n p*Z)) (historyNoise n) :=
    integrable_finsetSum _ (fun k _ => (hq k).integrable_sq)
  unfold actualLoss
  simp_rw [rowSq_sub]
  have hb : Integrable (fun p => rowSq B-2*rowInner B (errorRow (fun i => some (codes i)) origin step weight U n p*Z)) (historyNoise n) :=
    (integrable_const _).sub (hc.const_mul 2)
  rw [integral_add hb hs,integral_sub (integrable_const _) (hc.const_mul 2),integral_const,
    integral_const_mul,actual_finite_matched_output_energy codes origin step weight U hU pivot n d Z hgram]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  have hj : (∫ p,rowInner B (errorRow (fun i => some (codes i)) origin step weight U n p*Z) ∂historyNoise n)=
      rowInner B (meanOverloadOutput codes origin step weight U n d Z) := by
    unfold rowInner
    rw [integral_finsetSum Finset.univ (fun k _ => (MemLp.integrable (by norm_num) (hq k)).const_mul _)]
    simp_rw [integral_const_mul,actual_finite_output_mean codes origin step weight U hU n d Z]
    rfl
  rw [hj]; ring


theorem actual_loss_difference (codes : ℕ → ℕ) (origin step weight₀ weightα : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (hU : ∀ i j,j ≤ i → U i j=0) (pivot : ℕ → ℝ)
    (n d : ℕ) (Z : Matrix (Fin n) (Fin d) ℝ)
    (hgram : Z*Z.transpose=triangle U n*Matrix.diagonal (fun j : Fin n => pivot j.val)*(triangle U n).transpose)
    (A S : Row d) (alpha : ℝ) (hproj : rowInner A S=rowSq S) :
    actualLoss codes origin step weightα U n d Z (A-alpha • S)-actualLoss codes origin step weight₀ U n d Z A =
    -alpha*(2-alpha)*rowSq S-2*rowInner (A-alpha • S) (meanOverloadOutput codes origin step weightα U n d Z)+
      2*rowInner A (meanOverloadOutput codes origin step weight₀ U n d Z)+
      (∫ p,weightedOverload (fun i => some (codes i)) origin step weightα U pivot n p ∂historyNoise n)-
      (∫ p,weightedOverload (fun i => some (codes i)) origin step weight₀ U pivot n p ∂historyNoise n) := by
  rw [actual_loss_formula codes origin step weightα U hU pivot n d Z hgram,
      actual_loss_formula codes origin step weight₀ U hU pivot n d Z hgram,rowSq_sub]
  have hi : rowInner A (alpha • S)=alpha*rowInner A S := by
    unfold rowInner; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro k _; simp only [Matrix.smul_apply,smul_eq_mul]; ring
  have hs : rowSq (alpha • S)=alpha^2*rowSq S := by
    unfold rowSq; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro k _; simp only [Matrix.smul_apply,smul_eq_mul]; ring
  rw [hi,hs,hproj]; ring

end
end QepFeedbackLoss
