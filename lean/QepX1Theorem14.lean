import QepX1ProjectionActual
import QepX1ExpectationBridge

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
variable (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
    Mat (Fin (d (k+1))) (Fin (d (k+1))))





theorem actual_joint_psd_comparison
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hl : Legal d N W X0 a Eq pq L)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    PSDLe (covariance d N W X0 a Eq pq L)
      (covariance d N W X0 (fun _ => 0) Eb pb L) ∧
    PSDLe (outputMoment d N W X0 a Eq pq L)
      (outputMoment d N W X0 (fun _ => 0) Eb pb L) := by
  apply actual_joint_order_of_projection_bounds d N L W X0 a Eq Eb pq pb Ψ lawQ lawB
    hl hmQ hmB ha ha1
  · intro k hk ω hω
    exact actual_gram_error_bound _ _ _ (hl k hk ω hω) (ha k hk) (ha1 k hk)
  · intro k hk ω hω
    exact actual_gram_output_bound _ _ _ (hl k hk ω hω) (ha k hk) (ha1 k hk)

theorem actual_mse_comparison
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hl : Legal d N W X0 a Eq pq L)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    (∑ ω,pq ω*fSq (error d N W X0 a Eq L ω)) ≤
      ∑ ω,pb ω*fSq (error d N W X0 (fun _ => 0) Eb L ω) :=
  actual_mse_le_of_covariance_order d N L W X0 a Eq Eb pq pb
    (actual_joint_psd_comparison d N L W X0 a Eq Eb pq pb Ψ lawQ lawB hl hmQ hmB ha ha1).1



theorem actual_comparison_of_full_row_rank
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hrow : ∀ k < L,∀ ω,pq ω ≠ 0 → LinearIndependent ℝ (student d N W X0 a Eq k ω).row)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    PSDLe (covariance d N W X0 a Eq pq L)
      (covariance d N W X0 (fun _ => 0) Eb pb L) ∧
    PSDLe (outputMoment d N W X0 a Eq pq L)
      (outputMoment d N W X0 (fun _ => 0) Eb pb L) := by
  apply actual_joint_psd_comparison d N L W X0 a Eq Eb pq pb Ψ lawQ lawB _ hmQ hmB ha ha1
  intro k hk ω hω
  exact gram_isUnit_det_of_full_row_rank _ (hrow k hk ω hω)

variable [MeasurableSpace Ωq] [MeasurableSingletonClass Ωq]
  [MeasurableSpace Ωb] [MeasurableSingletonClass Ωb]




theorem actual_integral_comparison
    (μq : Measure Ωq) (μb : Measure Ωb) [IsProbabilityMeasure μq] [IsProbabilityMeasure μb]
    (hl : Legal d N W X0 a Eq (fun ω => μq.real {ω}) L)
    (hmQ : NoiseMoments d Eq (fun ω => μq.real {ω}) Ψ L)
    (hmB : NoiseMoments d Eb (fun ω => μb.real {ω}) Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    (∫ ω,fSq (error d N W X0 a Eq L ω) ∂μq) ≤
      ∫ ω,fSq (error d N W X0 (fun _ => 0) Eb L ω) ∂μb :=
  actual_integral_le_of_covariance_order d N L W X0 a Eq Eb μq μb
    (actual_joint_psd_comparison d N L W X0 a Eq Eb _ _ Ψ
      (probability_atoms_form_law μq) (probability_atoms_form_law μb) hl hmQ hmB ha ha1).1

end
end QepX1
