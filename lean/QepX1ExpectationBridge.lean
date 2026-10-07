import QepX1JointFinite
import QepX1FiniteIntegral

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace QepX1
noncomputable section
open MeasureTheory QepCorrected QepGram QepV3
open scoped BigOperators
variable {Ωq Ωb : Type*} [Fintype Ωq] [Fintype Ωb]
variable (d : ℕ → ℕ) (N L : ℕ)
variable (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
variable (X0 : Mat (Fin (d 0)) (Fin N)) (a : ℕ → ℝ)
variable (Eq : (k : ℕ) → Ωq → Mat (Fin (d (k+1))) (Fin (d k)))
variable (Eb : (k : ℕ) → Ωb → Mat (Fin (d (k+1))) (Fin (d k)))
variable (pq : Ωq → ℝ) (pb : Ωb → ℝ)



theorem actual_mse_le_of_covariance_order
    (hC : PSDLe (covariance d N W X0 a Eq pq L)
      (covariance d N W X0 (fun _ => 0) Eb pb L)) :
    (∑ ω,pq ω*fSq (error d N W X0 a Eq L ω)) ≤
      ∑ ω,pb ω*fSq (error d N W X0 (fun _ => 0) Eb L ω) := by
  have h := psdLe_trace _ _ hC
  simpa only [covariance,trace_mean_gram] using h

variable [MeasurableSpace Ωq] [MeasurableSingletonClass Ωq]
  [MeasurableSpace Ωb] [MeasurableSingletonClass Ωb]



theorem actual_integral_le_of_covariance_order
    (μq : Measure Ωq) (μb : Measure Ωb) [IsFiniteMeasure μq] [IsFiniteMeasure μb]
    (hC : PSDLe (covariance d N W X0 a Eq (fun ω => μq.real {ω}) L)
      (covariance d N W X0 (fun _ => 0) Eb (fun ω => μb.real {ω}) L)) :
    (∫ ω,fSq (error d N W X0 a Eq L ω) ∂μq) ≤
      ∫ ω,fSq (error d N W X0 (fun _ => 0) Eb L ω) ∂μb := by
  rw [← finite_fSq_integral μq,← finite_fSq_integral μb]
  exact actual_mse_le_of_covariance_order d N L W X0 a Eq Eb _ _ hC

end
end QepX1
