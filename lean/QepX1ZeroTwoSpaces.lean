import QepX1ZeroChecks

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepX1Zero
noncomputable section
open QepCorrected QepGram QepV3 QepX1
open scoped BigOperators

def wideP (_ : (Bool × Bool) × Bool) : ℝ := 1/8
def wideE (k : ℕ) (ω : (Bool × Bool) × Bool) := mixE k ω.1

theorem wide_law : FiniteLaw wideP := by
  constructor
  · intro ω; norm_num [wideP]
  · norm_num [wideP,Fintype.sum_prod_type,Fintype.sum_bool]

theorem wide_first_moments (k : ℕ) (hk : k < 2) :
    ConditionalMeanZero wideE k wideP (wideE k) := by
  interval_cases k
  · intro f hf i j
    have hconst (ω : (Bool × Bool) × Bool) : f ω = f ((false,false),false) :=
      hf ω ((false,false),false) (by intro j hj; omega)
    fin_cases i
    fin_cases j <;>
      norm_num [wideP,wideE,mixE,signQuarter,Fintype.sum_prod_type,Fintype.sum_bool,hconst]
  · intro f hf i j
    have hfib (u v b : Bool) : f ((u,v),b)=f ((u,false),false) := by
      apply hf
      intro j hj
      interval_cases j
      rfl
    fin_cases i
    fin_cases j
    norm_num [wideP,wideE,mixE,signQuarter,Fintype.sum_prod_type,Fintype.sum_bool,hfib]

theorem wide_noise_moments : NoiseMoments mixDim wideE wideP mixPsi 2 := by
  constructor
  · exact wide_first_moments
  · intro k hk
    apply entry_covariance_to_secondPSD wideE k wideP (wideE k) (mixK k)
    interval_cases k
    all_goals intro f _ i r j s
    all_goals fin_cases i
    all_goals fin_cases r
    all_goals fin_cases j
    all_goals fin_cases s
    all_goals norm_num [wideP,wideE,mixE,mixK,signQuarter,Fintype.sum_prod_type,Fintype.sum_bool]
    all_goals ring

theorem wide_student_eq (k : ℕ) (ω : (Bool × Bool) × Bool) :
    student mixDim 1 mixW mixX (fun _ => 0) wideE k ω =
      student mixDim 1 mixW mixX (fun _ => 0) mixE k ω.1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [base_student_step,wideE,ih]

theorem zero_two_spaces_main :
    PSDLe (covariance mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2)
      (covariance mixDim 1 mixW mixX (fun _ => 0) wideE wideP 2) ∧
    PSDLe (outputMoment mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2)
      (outputMoment mixDim 1 mixW mixX (fun _ => 0) wideE wideP 2) := by
  apply actual_joint_psd_comparison mixDim 1 2 mixW mixX (fun _ => 0) mixE wideE
    mixP wideP mixPsi mix_law wide_law
    (zero_schedule_positiveLegal mixDim 1 2 mixW mixX mixE mixP)
    mix_noise_moments wide_noise_moments
  · intro k hk; norm_num
  · intro k hk; norm_num

theorem zero_two_spaces_equal :
    covariance mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2 =
      covariance mixDim 1 mixW mixX (fun _ => 0) wideE wideP 2 ∧
    outputMoment mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2 =
      outputMoment mixDim 1 mixW mixX (fun _ => 0) wideE wideP 2 := by
  constructor
  all_goals ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp only [covariance,error,outputMoment,wide_student_eq,mean,mixP,wideP,
    Fintype.sum_prod_type,Fintype.sum_bool,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  all_goals ring

theorem zero_two_spaces_cardinality :
    Fintype.card (Bool × Bool) = 4 ∧ Fintype.card ((Bool × Bool) × Bool) = 8 := by
  norm_num

end
end QepX1Zero
