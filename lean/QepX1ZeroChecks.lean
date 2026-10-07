import QepX1ZeroNetwork
import QepX1EntryLaw
import QepX1Checks

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepX1Zero
noncomputable section
open QepCorrected QepGram QepV3 QepX1
open scoped BigOperators

def signQuarter (b : Bool) : ℝ := if b then 1/4 else -1/4
abbrev mixDim : ℕ → ℕ | 0 => 2 | _+1 => 1
def mixW : (k : ℕ) → Mat (Fin (mixDim (k+1))) (Fin (mixDim k))
  | 0 => !![1,0]
  | _+1 => !![1]
def mixX : Mat (Fin (mixDim 0)) (Fin 1) := !![1;1]
def mixAlpha : ℕ → ℝ | 0 => 0 | _+1 => 1
def mixE : (k : ℕ) → Bool × Bool → Mat (Fin (mixDim (k+1))) (Fin (mixDim k))
  | 0 => fun ω => !![signQuarter ω.1,0]
  | _+1 => fun ω => !![signQuarter ω.2]
def mixP (_ : Bool × Bool) : ℝ := 1/4
def mixK (k : ℕ) : Fin (mixDim (k+1)) → Fin (mixDim k) →
    Fin (mixDim (k+1)) → Fin (mixDim k) → ℝ :=
  fun _ r _ s => if r.val = 0 ∧ s.val = 0 then 1/16 else 0
def mixPsi (k : ℕ) := entryOperator (mixK k)

theorem mix_law : FiniteLaw mixP := by
  constructor
  · intro ω; norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixP]
  · norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixP,Fintype.sum_prod_type,Fintype.sum_bool]

theorem mix_first_moments (k : ℕ) (hk : k < 2) :
    ConditionalMeanZero mixE k mixP (mixE k) := by
  interval_cases k
  · intro f hf i j
    have hconst (ω : Bool × Bool) : f ω = f (false,false) :=
      hf ω (false,false) (by intro j hj; omega)
    fin_cases i
    fin_cases j <;>
      norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixP,mixE,signQuarter,Fintype.sum_prod_type,Fintype.sum_bool,hconst]
  · intro f hf i j
    have hfib (u : Bool) : f (u,true)=f (u,false) := by
      apply hf
      intro j hj
      interval_cases j
      rfl
    fin_cases i
    fin_cases j
    norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixP,mixE,signQuarter,Fintype.sum_prod_type,Fintype.sum_bool,hfib]

theorem mix_entry_covariances (k : ℕ) (hk : k < 2) :
    ConditionalEntryCovariance mixE k mixP (mixE k) (mixK k) := by
  interval_cases k
  all_goals intro f _ i r j s
  all_goals fin_cases i
  all_goals fin_cases r
  all_goals fin_cases j
  all_goals fin_cases s
  all_goals norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixP,mixE,mixK,signQuarter,Fintype.sum_prod_type,Fintype.sum_bool]
  all_goals ring

theorem mix_noise_moments : NoiseMoments mixDim mixE mixP mixPsi 2 := by
  constructor
  · exact mix_first_moments
  · intro k hk
    exact entry_covariance_to_secondPSD mixE k mixP (mixE k) (mixK k)
      (mix_entry_covariances k hk)

theorem mix_first_student (a : ℕ → ℝ) (ha : a 0 = 0) (ω : Bool × Bool) :
    student mixDim 1 mixW mixX a mixE 1 ω = !![1+signQuarter ω.1] := by
  rw [mixed_zero_student_step mixDim 1 mixW mixX a mixE 0 ω ha]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,student,mixW,mixE,mixX,Matrix.mul_apply,Fin.sum_univ_two]

theorem mix_initial_singular : ¬IsUnit (gram mixX).det := by
  norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixX,gram,Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_succ]

theorem mix_positive_legal : PositiveLegal mixDim 1 2 mixW mixX mixAlpha mixE mixP := by
  intro k hk hpos ω _
  interval_cases k
  · norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixAlpha] at hpos
  · rw [mix_first_student mixAlpha rfl]
    rcases ω with ⟨u,v⟩
    cases u <;> norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,gram,signQuarter,Matrix.det_fin_one,Matrix.mul_apply,Fin.sum_univ_succ]

theorem mix_not_old_legal : ¬Legal mixDim 1 mixW mixX mixAlpha mixE mixP 2 := by
  intro h
  exact mix_initial_singular (h 0 (by norm_num) (false,false) (by norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixP]))

theorem mix_main_instantiated :
    PSDLe (covariance mixDim 1 mixW mixX mixAlpha mixE mixP 2)
      (covariance mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2) ∧
    PSDLe (outputMoment mixDim 1 mixW mixX mixAlpha mixE mixP 2)
      (outputMoment mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2) := by
  apply actual_joint_psd_comparison mixDim 1 2 mixW mixX mixAlpha mixE mixE
    mixP mixP mixPsi mix_law mix_law mix_positive_legal mix_noise_moments mix_noise_moments
  · intro k hk; interval_cases k <;> norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixAlpha]
  · intro k hk; interval_cases k <;> norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixAlpha]

theorem mix_actual_outputs (u v : Bool) :
    student mixDim 1 mixW mixX mixAlpha mixE 2 (u,v) =
      !![1+signQuarter v*(1+signQuarter u)] ∧
    student mixDim 1 mixW mixX (fun _ => 0) mixE 2 (u,v) =
      !![(1+signQuarter v)*(1+signQuarter u)] := by
  constructor
  · change (correctedWeight (mixW 1) (teacher mixDim 1 mixW mixX 1)
      (student mixDim 1 mixW mixX mixAlpha mixE 1 (u,v)) (mixAlpha 1)+mixE 1 (u,v))*
        student mixDim 1 mixW mixX mixAlpha mixE 1 (u,v) = _
    rw [mix_first_student mixAlpha rfl]
    cases u <;> cases v <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixW,mixE,mixAlpha,teacher,mixX,signQuarter,correctedWeight,correction,
        gram,Matrix.inv_subsingleton,Ring.inverse_eq_inv,Matrix.mul_apply,Fin.sum_univ_succ]
  · rw [base_student_step,mix_first_student (fun _ => 0) rfl]
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixW,mixE,Matrix.mul_apply,Fin.sum_univ_succ]

theorem mix_exact_covariances :
    covariance mixDim 1 mixW mixX mixAlpha mixE mixP 2 = !![17/256] ∧
    covariance mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2 = !![33/256] := by
  constructor
  all_goals ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp only [covariance,error,(mix_actual_outputs _ _).1,(mix_actual_outputs _ _).2]
  all_goals norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mean,mixP,Fintype.sum_prod_type,Fintype.sum_bool,
    (mix_actual_outputs _ _).1,(mix_actual_outputs _ _).2,teacher,mixW,mixX,
    signQuarter,Matrix.mul_apply,Fin.sum_univ_succ]

theorem mix_exact_output_moments :
    outputMoment mixDim 1 mixW mixX mixAlpha mixE mixP 2 = !![273/256] ∧
    outputMoment mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2 = !![289/256] := by
  constructor
  all_goals ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,outputMoment,mean,mixP,Fintype.sum_prod_type,Fintype.sum_bool,
    (mix_actual_outputs _ _).1,(mix_actual_outputs _ _).2,signQuarter,
    Matrix.mul_apply,Fin.sum_univ_succ]

theorem mix_strictly_different :
    covariance mixDim 1 mixW mixX mixAlpha mixE mixP 2 ≠
      covariance mixDim 1 mixW mixX (fun _ => 0) mixE mixP 2 := by
  rw [mix_exact_covariances.1,mix_exact_covariances.2]
  intro h
  have hh := congrArg (fun M : Mat (Fin 1) (Fin 1) => M 0 0) h
  norm_num at hh

theorem mix_positive_first_illegal :
    ¬PositiveLegal mixDim 1 2 mixW mixX (fun _ => 1) mixE mixP := by
  intro h
  exact mix_initial_singular (h 0 (by norm_num) (by norm_num) (false,false) (by norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixP]))

theorem singular_projection_not_fixing : mixX*gramProjection mixX ≠ mixX := by
  rw [gramProjection,Matrix.nonsing_inv_apply_not_isUnit _ mix_initial_singular,
    Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_zero]
  intro h
  have hh := congrArg (fun M : Mat (Fin 2) (Fin 1) => M 0 0) h
  norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixDim,mixX] at hh

end
end QepX1Zero
