import QepX1OrderBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace QepX1
noncomputable section
open QepCorrected QepGram QepV3
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem convex_psdLe_upper (A T B : Mat n n) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hAB : PSDLe A B) (hTB : PSDLe T B) :
    PSDLe ((1-a) • A+a • T) B := by
  have h := (hAB.smul (sub_nonneg.mpr ha1)).add (hTB.smul ha)
  have he : (1-a) • (B-A)+a • (B-T)=B-((1-a) • A+a • T) := by
    simp only [smul_sub,sub_smul,one_smul]
    abel
  change (B-((1-a) • A+a • T)).PosSemidef
  rw [← he]
  exact h

variable {Ωq Ωb : Type*} [Fintype Ωq] [Fintype Ωb]
variable (d : ℕ → ℕ) (N L : ℕ)
variable (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
variable (X0 : Mat (Fin (d 0)) (Fin N)) (a : ℕ → ℝ)
variable (Eq : (k : ℕ) → Ωq → Mat (Fin (d (k+1))) (Fin (d k)))
variable (Eb : (k : ℕ) → Ωb → Mat (Fin (d (k+1))) (Fin (d k)))
variable (pq : Ωq → ℝ) (pb : Ωb → ℝ)
variable (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
    Mat (Fin (d (k+1))) (Fin (d (k+1))))




theorem actual_joint_order_of_projection_bounds
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hl : Legal d N W X0 a Eq pq L)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1)
    (herror : ∀ k < L,∀ ω,pq ω ≠ 0 →
      PSDLe ((correctedInput (teacher d N W X0 k) (student d N W X0 a Eq k ω) (a k)-
        teacher d N W X0 k)*(correctedInput (teacher d N W X0 k)
        (student d N W X0 a Eq k ω) (a k)-teacher d N W X0 k).transpose)
      ((student d N W X0 a Eq k ω-teacher d N W X0 k)*
        (student d N W X0 a Eq k ω-teacher d N W X0 k).transpose))
    (houtput : ∀ k < L,∀ ω,pq ω ≠ 0 →
      PSDLe (correctedInput (teacher d N W X0 k) (student d N W X0 a Eq k ω) (a k)*
        (correctedInput (teacher d N W X0 k) (student d N W X0 a Eq k ω) (a k)).transpose)
      ((1-a k) • (student d N W X0 a Eq k ω*(student d N W X0 a Eq k ω).transpose)+
        a k • (teacher d N W X0 k*(teacher d N W X0 k).transpose))) :
    PSDLe (covariance d N W X0 a Eq pq L)
      (covariance d N W X0 (fun _ => 0) Eb pb L) ∧
    PSDLe (outputMoment d N W X0 a Eq pq L)
      (outputMoment d N W X0 (fun _ => 0) Eb pb L) := by
  have hall : ∀ k ≤ L,
      PSDLe (covariance d N W X0 a Eq pq k)
        (covariance d N W X0 (fun _ => 0) Eb pb k) ∧
      PSDLe (outputMoment d N W X0 a Eq pq k)
        (outputMoment d N W X0 (fun _ => 0) Eb pb k) := by
    intro k hk
    induction k with
    | zero =>
      constructor
      · simp only [covariance,error,student,teacher,sub_self,Matrix.transpose_zero,
          Matrix.mul_zero,mean_zero]
        exact psdLe_refl _
      · simp only [outputMoment,student,mean_const pq _ lawQ.mass,mean_const pb _ lawB.mass]
        exact psdLe_refl _
    | succ k ih =>
      have hkL : k < L := by omega
      obtain ⟨hC,hG⟩ := ih (by omega)
      have hΨ : ∀ V : Mat (Fin (d k)) (Fin (d k)),V.PosSemidef → (Ψ k V).PosSemidef :=
        secondPSD_operator_positive Eq k pq (Eq k) (Ψ k) lawQ (hmQ.second k hkL)
      have hnoise := psdLe_linear_map (Ψ k) hΨ hG
      have hT : PSDLe (teacher d N W X0 k*(teacher d N W X0 k).transpose)
          (outputMoment d N W X0 (fun _ => 0) Eb pb k) := by
        rw [base_output_equals_teacher_plus_covariance d N W X0 Eb pb L Ψ lawB hmB k (by omega)]
        unfold PSDLe
        rw [add_sub_cancel_left]
        exact actual_covariance_posSemidef d N W X0 (fun _ => 0) Eb pb lawB k
      constructor
      · have hlocal := actual_qep_error_le_of_pointwise Eq k pq (Eq k)
          (student d N W X0 a Eq k) (W k) (teacher d N W X0 k) (a k) (Ψ k) lawQ
          (past_student d N W X0 a Eq k) (hmQ.first k hkL) (hmQ.second k hkL)
          (hl k hkL) (herror k hkL)
        change PSDLe (covariance d N W X0 a Eq pq (k+1))
          (W k*covariance d N W X0 a Eq pq k*(W k).transpose+
            Ψ k (outputMoment d N W X0 a Eq pq k)) at hlocal
        rw [base_error_moment_step d N W X0 Eb pb L Ψ hmB k hkL]
        exact psdLe_trans _ _ _ hlocal (psdLe_add (psdLe_congruence (W k) hC) hnoise)
      · have hlocal := actual_qep_output_le_of_pointwise Eq k pq (Eq k)
          (student d N W X0 a Eq k) (W k) (teacher d N W X0 k) (a k) (Ψ k) lawQ
          (past_student d N W X0 a Eq k) (hmQ.first k hkL) (hmQ.second k hkL)
          (hl k hkL) (houtput k hkL)
        change PSDLe (outputMoment d N W X0 a Eq pq (k+1))
          (W k*((1-a k) • outputMoment d N W X0 a Eq pq k+
            a k • (teacher d N W X0 k*(teacher d N W X0 k).transpose))*(W k).transpose+
              Ψ k (outputMoment d N W X0 a Eq pq k)) at hlocal
        rw [base_output_moment_step d N W X0 Eb pb L Ψ hmB k hkL]
        exact psdLe_trans _ _ _ hlocal (psdLe_add (psdLe_congruence (W k)
          (convex_psdLe_upper _ _ _ (a k) (ha k hkL) (ha1 k hkL) hG hT)) hnoise)
  exact hall L le_rfl

end
end QepX1
