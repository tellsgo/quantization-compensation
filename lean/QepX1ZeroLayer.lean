import QepX1Theorem14

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace QepX1Zero
noncomputable section
open QepCorrected QepGram QepV3 QepX1
open scoped BigOperators
variable {Ω m n t : Type*} [Fintype Ω] [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]



theorem correctedWeight_zero (W : Mat m n) (X Z : Mat n t) :
    correctedWeight W X Z 0 = W := by simp [correctedWeight]

theorem correctedInput_zero (X Z : Mat n t) : correctedInput X Z 0 = Z := by
  simp [correctedInput]


theorem actual_output_identity (W E : Mat m n) (X Z : Mat n t) (a : ℝ)
    (hZ : a = 0 ∨ IsUnit (gram Z).det) :
    (correctedWeight W X Z a+E)*Z = W*correctedInput X Z a+E*Z := by
  rcases hZ with h0 | hlegal
  · subst a
    simp [correctedWeight_zero, correctedInput_zero, Matrix.add_mul]
  · exact QepX1.actual_output_identity W E X Z a hlegal

theorem actual_gram_error_bound (X Z : Mat n t) (a : ℝ)
    (hZ : a = 0 ∨ IsUnit (gram Z).det) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    PSDLe ((correctedInput X Z a-X)*(correctedInput X Z a-X).transpose)
      ((Z-X)*(Z-X).transpose) := by
  rcases hZ with h0 | hlegal
  · subst a
    rw [correctedInput_zero]
    exact psdLe_refl _
  · exact QepX1.actual_gram_error_bound X Z a hlegal ha ha1

theorem actual_gram_output_bound (X Z : Mat n t) (a : ℝ)
    (hZ : a = 0 ∨ IsUnit (gram Z).det) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    PSDLe (correctedInput X Z a*(correctedInput X Z a).transpose)
      ((1-a) • (Z*Z.transpose)+a • (X*X.transpose)) := by
  rcases hZ with h0 | hlegal
  · subst a
    simpa only [correctedInput_zero,sub_zero,one_smul,zero_smul,add_zero]
      using psdLe_refl (Z*Z.transpose)
  · exact QepX1.actual_gram_output_bound X Z a hlegal ha ha1

variable {H : ℕ → Type*} (history : (k : ℕ) → Ω → H k) (k : ℕ)
variable (p : Ω → ℝ) (E : Ω → Mat m n) (Z : Ω → Mat n t)
variable (W : Mat m n) (X : Mat n t) (a : ℝ)
variable (Ψ : Mat n n →ₗ[ℝ] Mat m m)


theorem actual_qep_first_moment (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hgram : ∀ ω,p ω ≠ 0 → a = 0 ∨ IsUnit (gram (Z ω)).det) :
    mean p (fun ω => (correctedWeight W X (Z ω) a+E ω)*Z ω) =
      W*mean p (fun ω => correctedInput X (Z ω) a) := by
  have he : mean p (fun ω => (correctedWeight W X (Z ω) a+E ω)*Z ω) =
      mean p (fun ω => W*correctedInput X (Z ω) a+E ω*Z ω) := by
    apply mean_support_congr
    intro ω hω
    exact actual_output_identity W (E ω) X (Z ω) a (hgram ω hω)
  rw [he,mean_add,mean_const_mul,
    mean_noise_mul_zero history k p E Z hZpast hfirst,add_zero]


theorem actual_qep_output_moment
    (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → a = 0 ∨ IsUnit (gram (Z ω)).det) :
    mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω).transpose)=
      W*mean p (fun ω => correctedInput X (Z ω) a*(correctedInput X (Z ω) a).transpose)*W.transpose+
      Ψ (mean p (fun ω => Z ω*(Z ω).transpose)) := by
  have he : mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω).transpose)=
      mean p (fun ω => (W*correctedInput X (Z ω) a+E ω*Z ω)*
        (W*correctedInput X (Z ω) a+E ω*Z ω).transpose) := by
    apply mean_support_congr
    intro ω hω
    rw [actual_output_identity W (E ω) X (Z ω) a (hgram ω hω)]
  rw [he,affine_actual_second_moment history k p E Z
    (fun ω => W*correctedInput X (Z ω) a) Ψ hZpast
    (past_map history k Z (fun M => W*correctedInput X M a) hZpast) hfirst hsecond,
    mean_congruence]



theorem actual_qep_error_moment
    (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → a = 0 ∨ IsUnit (gram (Z ω)).det) :
    mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X).transpose)=
      W*mean p (fun ω => (correctedInput X (Z ω) a-X)*
        (correctedInput X (Z ω) a-X).transpose)*W.transpose+
      Ψ (mean p (fun ω => Z ω*(Z ω).transpose)) := by
  have he : mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X).transpose)=
      mean p (fun ω => (W*(correctedInput X (Z ω) a-X)+E ω*Z ω)*
        (W*(correctedInput X (Z ω) a-X)+E ω*Z ω).transpose) := by
    apply mean_support_congr
    intro ω hω
    rw [actual_output_identity W (E ω) X (Z ω) a (hgram ω hω)]
    have hh : W*correctedInput X (Z ω) a+E ω*Z ω-W*X =
        W*(correctedInput X (Z ω) a-X)+E ω*Z ω := by rw [Matrix.mul_sub]; abel
    rw [hh]
  rw [he,affine_actual_second_moment history k p E Z
    (fun ω => W*(correctedInput X (Z ω) a-X)) Ψ hZpast
    (past_map history k Z (fun M => W*(correctedInput X M a-X)) hZpast) hfirst hsecond,
    mean_congruence]



theorem actual_qep_error_le_of_pointwise {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (Z : Ω → Mat n t) (W : Mat m n) (X : Mat n t) (a : ℝ)
    (Ψ : Mat n n →ₗ[ℝ] Mat m m) (law : FiniteLaw p)
    (hZpast : Past history k Z) (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → a = 0 ∨ IsUnit (gram (Z ω)).det)
    (hpoint : ∀ ω,p ω ≠ 0 →
      PSDLe ((correctedInput X (Z ω) a-X)*(correctedInput X (Z ω) a-X).transpose)
        ((Z ω-X)*(Z ω-X).transpose)) :
    PSDLe (mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X).transpose))
      (W*mean p (fun ω => (Z ω-X)*(Z ω-X).transpose)*W.transpose+
        Ψ (mean p (fun ω => Z ω*(Z ω).transpose))) := by
  rw [actual_qep_error_moment history k p E Z W X a Ψ hZpast hfirst hsecond hgram]
  exact psdLe_add (psdLe_congruence W (mean_psdLe_support p _ _ law.nonnegative hpoint))
    (psdLe_refl _)



theorem actual_qep_output_le_of_pointwise {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (Z : Ω → Mat n t) (W : Mat m n) (X : Mat n t) (a : ℝ)
    (Ψ : Mat n n →ₗ[ℝ] Mat m m) (law : FiniteLaw p)
    (hZpast : Past history k Z) (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → a = 0 ∨ IsUnit (gram (Z ω)).det)
    (hpoint : ∀ ω,p ω ≠ 0 →
      PSDLe (correctedInput X (Z ω) a*(correctedInput X (Z ω) a).transpose)
        ((1-a) • (Z ω*(Z ω).transpose)+a • (X*X.transpose))) :
    PSDLe (mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω).transpose))
      (W*((1-a) • mean p (fun ω => Z ω*(Z ω).transpose)+a • (X*X.transpose))*W.transpose+
        Ψ (mean p (fun ω => Z ω*(Z ω).transpose))) := by
  rw [actual_qep_output_moment history k p E Z W X a Ψ hZpast hfirst hsecond hgram]
  have hh := mean_psdLe_support p _ _ law.nonnegative hpoint
  simp only [mean_add,mean_smul,mean_const p _ law.mass] at hh
  exact psdLe_add (psdLe_congruence W hh) (psdLe_refl _)

end
end QepX1Zero
