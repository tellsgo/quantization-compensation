import QepX1ZeroChecks

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepX1Zero
noncomputable section
open QepCorrected QepGram QepV3 QepX1
open scoped BigOperators

abbrev nullDim (_ : ℕ) : ℕ := 1
def nullW (_ : ℕ) : Mat (Fin 1) (Fin 1) := !![1]
def nullX : Mat (Fin 1) (Fin 1) := !![1]
def nullP : Fin 3 → ℝ := ![1/2,1/2,0]
def nullFirst : Fin 3 → ℝ := ![1/4,-1/4,-1]
def nullE (k : ℕ) (ω : Fin 3) : Mat (Fin 1) (Fin 1) :=
  if k = 0 then !![nullFirst ω] else 0
def nullK (k : ℕ) (_ _ _ _ : Fin 1) : ℝ := if k = 0 then 1/16 else 0
def nullPsi (k : ℕ) := entryOperator (nullK k)

theorem null_law : FiniteLaw nullP := by
  constructor
  · intro ω; fin_cases ω <;> norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullP]
  · norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullP,Fin.sum_univ_succ]

theorem null_noise_moments : NoiseMoments nullDim nullE nullP nullPsi 2 := by
  constructor
  · intro k hk f hf i j
    interval_cases k
    · have hconst (ω : Fin 3) : f ω = f 0 := hf ω 0 (by intro j hj; omega)
      fin_cases i
      fin_cases j
      norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullDim,nullP,nullE,nullFirst,hconst,Fin.sum_univ_succ]
    · simp [nullE]
  · intro k hk
    apply entry_covariance_to_secondPSD nullE k nullP (nullE k) (nullK k)
    intro f _ i r j s
    interval_cases k
    all_goals fin_cases i
    all_goals fin_cases r
    all_goals fin_cases j
    all_goals fin_cases s
    all_goals norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullDim,nullE,nullK,nullP,nullFirst,Fin.sum_univ_succ]
    all_goals ring

theorem null_first_student (a : ℕ → ℝ) (ha : a 0 = 0) (ω : Fin 3) :
    student nullDim 1 nullW nullX a nullE 1 ω = !![1+nullFirst ω] := by
  rw [mixed_zero_student_step nullDim 1 nullW nullX a nullE 0 ω ha]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullDim,student,nullW,nullE,nullX,Matrix.mul_apply,Fin.sum_univ_succ]

theorem null_positive_legal :
    PositiveLegal nullDim 1 2 nullW nullX mixAlpha nullE nullP := by
  intro k hk hpos ω hω
  interval_cases k
  · norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixAlpha] at hpos
  · rw [null_first_student mixAlpha rfl]
    fin_cases ω <;>
      norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullP,nullFirst,gram,Matrix.det_fin_one,Matrix.mul_apply,Fin.sum_univ_succ] at *

theorem null_supported_singular_witness :
    nullP 2 = 0 ∧ student nullDim 1 nullW nullX mixAlpha nullE 1 2 = 0 := by
  constructor
  · rfl
  · rw [null_first_student mixAlpha rfl]
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullDim,nullFirst]

theorem null_all_atoms_legal_false :
    ¬(∀ ω,IsUnit (gram (student nullDim 1 nullW nullX mixAlpha nullE 1 ω)).det) := by
  intro h
  have hh := h 2
  rw [null_supported_singular_witness.2] at hh
  norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,gram] at hh

theorem null_main_instantiated :
    PSDLe (covariance nullDim 1 nullW nullX mixAlpha nullE nullP 2)
      (covariance nullDim 1 nullW nullX (fun _ => 0) nullE nullP 2) ∧
    PSDLe (outputMoment nullDim 1 nullW nullX mixAlpha nullE nullP 2)
      (outputMoment nullDim 1 nullW nullX (fun _ => 0) nullE nullP 2) := by
  apply actual_joint_psd_comparison nullDim 1 2 nullW nullX mixAlpha nullE nullE
    nullP nullP nullPsi null_law null_law null_positive_legal null_noise_moments null_noise_moments
  · intro k hk; interval_cases k <;> norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixAlpha]
  · intro k hk; interval_cases k <;> norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,mixAlpha]

theorem null_actual_outputs (ω : Fin 3) :
    student nullDim 1 nullW nullX mixAlpha nullE 2 ω = !![if ω = 2 then 0 else 1] ∧
    student nullDim 1 nullW nullX (fun _ => 0) nullE 2 ω = !![1+nullFirst ω] := by
  constructor
  · change (correctedWeight (nullW 1) (teacher nullDim 1 nullW nullX 1)
      (student nullDim 1 nullW nullX mixAlpha nullE 1 ω) (mixAlpha 1)+nullE 1 ω)*
        student nullDim 1 nullW nullX mixAlpha nullE 1 ω = _
    rw [null_first_student mixAlpha rfl]
    fin_cases ω <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullDim,nullW,nullE,mixAlpha,teacher,nullX,nullFirst,correctedWeight,
        correction,gram,Matrix.inv_subsingleton,Ring.inverse_eq_inv,Matrix.mul_apply,Fin.sum_univ_succ]
  · rw [base_student_step,null_first_student (fun _ => 0) rfl]
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullDim,nullW,nullE,Matrix.mul_apply,Fin.sum_univ_succ]

theorem null_exact_moments :
    covariance nullDim 1 nullW nullX mixAlpha nullE nullP 2 = !![0] ∧
    covariance nullDim 1 nullW nullX (fun _ => 0) nullE nullP 2 = !![1/16] ∧
    outputMoment nullDim 1 nullW nullX mixAlpha nullE nullP 2 = !![1] ∧
    outputMoment nullDim 1 nullW nullX (fun _ => 0) nullE nullP 2 = !![17/16] := by
  repeat' constructor
  all_goals ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp only [covariance,error,outputMoment,
    (null_actual_outputs _).1,(null_actual_outputs _).2]
  all_goals norm_num [Matrix.vecMul,Matrix.vecHead,dotProduct,nullDim,mean,nullP,nullFirst,teacher,nullW,nullX,
    Matrix.mul_apply,Fin.sum_univ_succ]

end
end QepX1Zero
