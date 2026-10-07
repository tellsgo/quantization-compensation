import QepX1ZeroLayer

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace QepX1Zero
noncomputable section
open MeasureTheory QepCorrected QepGram QepV3 QepX1
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



def PositiveLegal : Prop :=
  ∀ k < L, 0 < a k → ∀ ω,pq ω ≠ 0 →
    IsUnit (gram (student d N W X0 a Eq k ω)).det

theorem positiveLegal_cases (hl : PositiveLegal d N L W X0 a Eq pq)
    (ha : ∀ k < L,0 ≤ a k) (k : ℕ) (hk : k < L) (ω : Ωq) (hω : pq ω ≠ 0) :
    a k = 0 ∨ IsUnit (gram (student d N W X0 a Eq k ω)).det := by
  by_cases hz : a k = 0
  · exact Or.inl hz
  · exact Or.inr (hl k hk (lt_of_le_of_ne (ha k hk) (Ne.symm hz)) ω hω)

theorem old_legal_implies_positiveLegal (hl : Legal d N W X0 a Eq pq L) :
    PositiveLegal d N L W X0 a Eq pq := by
  intro k hk _ ω hω
  exact hl k hk ω hω

theorem zero_schedule_positiveLegal : PositiveLegal d N L W X0 (fun _ => 0) Eq pq := by
  intro k hk ha
  norm_num at ha

theorem mixed_zero_student_step (k : ℕ) (ω : Ωq) (ha : a k = 0) :
    student d N W X0 a Eq (k+1) ω = (W k+Eq k ω)*student d N W X0 a Eq k ω := by
  simp only [student,ha,correctedWeight_zero]




theorem actual_joint_order_of_projection_bounds
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hl : PositiveLegal d N L W X0 a Eq pq)
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
          (positiveLegal_cases d N L W X0 a Eq pq hl ha k hkL) (herror k hkL)
        change PSDLe (covariance d N W X0 a Eq pq (k+1))
          (W k*covariance d N W X0 a Eq pq k*(W k).transpose+
            Ψ k (outputMoment d N W X0 a Eq pq k)) at hlocal
        rw [base_error_moment_step d N W X0 Eb pb L Ψ hmB k hkL]
        exact psdLe_trans _ _ _ hlocal (psdLe_add (psdLe_congruence (W k) hC) hnoise)
      · have hlocal := actual_qep_output_le_of_pointwise Eq k pq (Eq k)
          (student d N W X0 a Eq k) (W k) (teacher d N W X0 k) (a k) (Ψ k) lawQ
          (past_student d N W X0 a Eq k) (hmQ.first k hkL) (hmQ.second k hkL)
          (positiveLegal_cases d N L W X0 a Eq pq hl ha k hkL) (houtput k hkL)
        change PSDLe (outputMoment d N W X0 a Eq pq (k+1))
          (W k*((1-a k) • outputMoment d N W X0 a Eq pq k+
            a k • (teacher d N W X0 k*(teacher d N W X0 k).transpose))*(W k).transpose+
              Ψ k (outputMoment d N W X0 a Eq pq k)) at hlocal
        rw [base_output_moment_step d N W X0 Eb pb L Ψ hmB k hkL]
        exact psdLe_trans _ _ _ hlocal (psdLe_add (psdLe_congruence (W k)
          (convex_psdLe_upper _ _ _ (a k) (ha k hkL) (ha1 k hkL) hG hT)) hnoise)
  exact hall L le_rfl




theorem actual_joint_psd_comparison
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hl : PositiveLegal d N L W X0 a Eq pq)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    PSDLe (covariance d N W X0 a Eq pq L)
      (covariance d N W X0 (fun _ => 0) Eb pb L) ∧
    PSDLe (outputMoment d N W X0 a Eq pq L)
      (outputMoment d N W X0 (fun _ => 0) Eb pb L) := by
  apply actual_joint_order_of_projection_bounds d N L W X0 a Eq Eb pq pb Ψ lawQ lawB
    hl hmQ hmB ha ha1
  · intro k hk ω hω
    exact actual_gram_error_bound _ _ _ (positiveLegal_cases d N L W X0 a Eq pq hl ha k hk ω hω) (ha k hk) (ha1 k hk)
  · intro k hk ω hω
    exact actual_gram_output_bound _ _ _ (positiveLegal_cases d N L W X0 a Eq pq hl ha k hk ω hω) (ha k hk) (ha1 k hk)

theorem actual_mse_comparison
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hl : PositiveLegal d N L W X0 a Eq pq)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    (∑ ω,pq ω*fSq (error d N W X0 a Eq L ω)) ≤
      ∑ ω,pb ω*fSq (error d N W X0 (fun _ => 0) Eb L ω) :=
  actual_mse_le_of_covariance_order d N L W X0 a Eq Eb pq pb
    (actual_joint_psd_comparison d N L W X0 a Eq Eb pq pb Ψ lawQ lawB hl hmQ hmB ha ha1).1



theorem actual_comparison_of_full_row_rank
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hrow : ∀ k < L,0 < a k → ∀ ω,pq ω ≠ 0 → LinearIndependent ℝ (student d N W X0 a Eq k ω).row)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    PSDLe (covariance d N W X0 a Eq pq L)
      (covariance d N W X0 (fun _ => 0) Eb pb L) ∧
    PSDLe (outputMoment d N W X0 a Eq pq L)
      (outputMoment d N W X0 (fun _ => 0) Eb pb L) := by
  apply actual_joint_psd_comparison d N L W X0 a Eq Eb pq pb Ψ lawQ lawB _ hmQ hmB ha ha1
  intro k hk hpos ω hω
  exact gram_isUnit_det_of_full_row_rank _ (hrow k hk hpos ω hω)

variable [MeasurableSpace Ωq] [MeasurableSingletonClass Ωq]
  [MeasurableSpace Ωb] [MeasurableSingletonClass Ωb]




theorem actual_integral_comparison
    (μq : Measure Ωq) (μb : Measure Ωb) [IsProbabilityMeasure μq] [IsProbabilityMeasure μb]
    (hl : PositiveLegal d N L W X0 a Eq (fun ω => μq.real {ω}))
    (hmQ : NoiseMoments d Eq (fun ω => μq.real {ω}) Ψ L)
    (hmB : NoiseMoments d Eb (fun ω => μb.real {ω}) Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) :
    (∫ ω,fSq (error d N W X0 a Eq L ω) ∂μq) ≤
      ∫ ω,fSq (error d N W X0 (fun _ => 0) Eb L ω) ∂μb :=
  actual_integral_le_of_covariance_order d N L W X0 a Eq Eb μq μb
    (actual_joint_psd_comparison d N L W X0 a Eq Eb _ _ Ψ
      (probability_atoms_form_law μq) (probability_atoms_form_law μb) hl hmQ hmB ha ha1).1


theorem actual_prefix_comparison
    (lawQ : FiniteLaw pq) (lawB : FiniteLaw pb)
    (hl : PositiveLegal d N L W X0 a Eq pq)
    (hmQ : NoiseMoments d Eq pq Ψ L) (hmB : NoiseMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (ha1 : ∀ k < L,a k ≤ 1) (k : ℕ) (hk : k ≤ L) :
    PSDLe (covariance d N W X0 a Eq pq k)
      (covariance d N W X0 (fun _ => 0) Eb pb k) ∧
    PSDLe (outputMoment d N W X0 a Eq pq k)
      (outputMoment d N W X0 (fun _ => 0) Eb pb k) := by
  apply actual_joint_psd_comparison d N k W X0 a Eq Eb pq pb Ψ lawQ lawB
  · exact fun j hj hpos ω hω => hl j (lt_of_lt_of_le hj hk) hpos ω hω
  · exact ⟨fun j hj => hmQ.first j (lt_of_lt_of_le hj hk),
      fun j hj => hmQ.second j (lt_of_lt_of_le hj hk)⟩
  · exact ⟨fun j hj => hmB.first j (lt_of_lt_of_le hj hk),
      fun j hj => hmB.second j (lt_of_lt_of_le hj hk)⟩
  · exact fun j hj => ha j (lt_of_lt_of_le hj hk)
  · exact fun j hj => ha1 j (lt_of_lt_of_le hj hk)

end
end QepX1Zero
