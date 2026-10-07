import QepX1Conditional

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace QepX1
noncomputable section
open QepCorrected QepGram QepV3
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]
variable (d : ℕ → ℕ) (N : ℕ)
variable (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
variable (X0 : Mat (Fin (d 0)) (Fin N)) (a : ℕ → ℝ)
variable (E : (k : ℕ) → Ω → Mat (Fin (d (k+1))) (Fin (d k)))
variable (p : Ω → ℝ)


def outputMoment (k : ℕ) : Mat (Fin (d k)) (Fin (d k)) :=
  mean p (fun ω => student d N W X0 a E k ω*(student d N W X0 a E k ω).transpose)

structure NoiseMoments
    (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
      Mat (Fin (d (k+1))) (Fin (d (k+1)))) (L : ℕ) : Prop where
  first : ∀ k < L, ConditionalMeanZero E k p (E k)
  second : ∀ k < L, ConditionalSecondPSD E k p (E k) (Ψ k)

variable (L : ℕ)
variable (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
    Mat (Fin (d (k+1))) (Fin (d (k+1))))

theorem actual_output_moment_step
    (hl : Legal d N W X0 a E p L) (hm : NoiseMoments d E p Ψ L)
    (k : ℕ) (hk : k < L) :
    outputMoment d N W X0 a E p (k+1)=
      W k*mean p (fun ω =>
        correctedInput (teacher d N W X0 k) (student d N W X0 a E k ω) (a k)*
          (correctedInput (teacher d N W X0 k) (student d N W X0 a E k ω) (a k)).transpose)*
        (W k).transpose+Ψ k (outputMoment d N W X0 a E p k) := by
  exact actual_qep_output_moment E k p (E k) (student d N W X0 a E k)
    (W k) (teacher d N W X0 k) (a k) (Ψ k)
    (past_student d N W X0 a E k) (hm.first k hk) (hm.second k hk) (hl k hk)

theorem actual_error_moment_step
    (hl : Legal d N W X0 a E p L) (hm : NoiseMoments d E p Ψ L)
    (k : ℕ) (hk : k < L) :
    covariance d N W X0 a E p (k+1)=
      W k*mean p (fun ω =>
        (correctedInput (teacher d N W X0 k) (student d N W X0 a E k ω) (a k)-teacher d N W X0 k)*
        (correctedInput (teacher d N W X0 k) (student d N W X0 a E k ω) (a k)-teacher d N W X0 k).transpose)*
        (W k).transpose+Ψ k (outputMoment d N W X0 a E p k) := by
  exact actual_qep_error_moment E k p (E k) (student d N W X0 a E k)
    (W k) (teacher d N W X0 k) (a k) (Ψ k)
    (past_student d N W X0 a E k) (hm.first k hk) (hm.second k hk) (hl k hk)



theorem base_student_step (k : ℕ) (ω : Ω) :
    student d N W X0 (fun _ => 0) E (k+1) ω=
      (W k+E k ω)*student d N W X0 (fun _ => 0) E k ω := by
  simp [student,correctedWeight]


theorem base_unbiased (law : FiniteLaw p) (hm : NoiseMoments d E p Ψ L)
    (k : ℕ) (hk : k ≤ L) :
    mean p (student d N W X0 (fun _ => 0) E k)=teacher d N W X0 k := by
  induction k with
  | zero => exact mean_const p X0 law.mass
  | succ k ih =>
    change mean p (fun ω => student d N W X0 (fun _ => 0) E (k+1) ω)=_
    simp only [base_student_step]
    rw [actual_base_mean E k p (E k) (student d N W X0 (fun _ => 0) E k) (W k)
      (past_student d N W X0 (fun _ => 0) E k) (hm.first k (by omega)),ih (by omega)]
    rfl

theorem base_centered (law : FiniteLaw p) (hm : NoiseMoments d E p Ψ L)
    (k : ℕ) (hk : k ≤ L) : mean p (error d N W X0 (fun _ => 0) E k)=0 := by
  unfold error
  rw [mean_sub,base_unbiased d N W X0 E p L Ψ law hm k hk,
    mean_const p _ law.mass,sub_self]

theorem base_output_equals_teacher_plus_covariance (law : FiniteLaw p)
    (hm : NoiseMoments d E p Ψ L) (k : ℕ) (hk : k ≤ L) :
    outputMoment d N W X0 (fun _ => 0) E p k=
      teacher d N W X0 k*(teacher d N W X0 k).transpose+
        covariance d N W X0 (fun _ => 0) E p k := by
  have hh := mean_shifted_gram p (error d N W X0 (fun _ => 0) E k)
    (teacher d N W X0 k) law.mass (base_centered d N W X0 E p L Ψ law hm k hk)
  calc
    _ = covariance d N W X0 (fun _ => 0) E p k+
        teacher d N W X0 k*(teacher d N W X0 k).transpose := by
      simpa only [error,sub_add_cancel,covariance,outputMoment] using hh
    _ = _ := add_comm _ _

theorem base_output_moment_step (hm : NoiseMoments d E p Ψ L)
    (k : ℕ) (hk : k < L) :
    outputMoment d N W X0 (fun _ => 0) E p (k+1)=
      W k*outputMoment d N W X0 (fun _ => 0) E p k*(W k).transpose+
        Ψ k (outputMoment d N W X0 (fun _ => 0) E p k) := by
  unfold outputMoment
  simp only [base_student_step]
  exact actual_base_output_moment E k p (E k) (student d N W X0 (fun _ => 0) E k)
    (W k) (Ψ k) (past_student d N W X0 (fun _ => 0) E k) (hm.first k hk) (hm.second k hk)

theorem base_error_moment_step (hm : NoiseMoments d E p Ψ L)
    (k : ℕ) (hk : k < L) :
    covariance d N W X0 (fun _ => 0) E p (k+1)=
      W k*covariance d N W X0 (fun _ => 0) E p k*(W k).transpose+
        Ψ k (outputMoment d N W X0 (fun _ => 0) E p k) := by
  unfold covariance error
  simp only [base_student_step,teacher]
  exact actual_base_error_moment E k p (E k) (student d N W X0 (fun _ => 0) E k)
    (W k) (teacher d N W X0 k) (Ψ k)
    (past_student d N W X0 (fun _ => 0) E k) (hm.first k hk) (hm.second k hk)

end
end QepX1
