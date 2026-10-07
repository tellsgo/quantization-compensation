import QepV3Network

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace QepX1
noncomputable section
open QepCorrected QepGram QepV3
open scoped BigOperators
variable {Ω m n t : Type*} [Fintype Ω] [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]


def correctedInput (X Z : Mat n t) (a : ℝ) : Mat n t :=
  (1-a) • Z+a • (X*gramProjection Z)

theorem actual_output_identity (W E : Mat m n) (X Z : Mat n t) (a : ℝ)
    (hZ : IsUnit (gram Z).det) :
    (correctedWeight W X Z a+E)*Z = W*correctedInput X Z a+E*Z := by
  simp only [correctedWeight,Matrix.add_mul,Matrix.smul_mul,correction_times_input,
    correctedInput,Matrix.mul_add,Matrix.mul_smul,Matrix.sub_mul,Matrix.mul_sub,
    Matrix.mul_assoc,input_times_projection Z hZ,sub_smul,one_smul,smul_sub]
  abel




def ConditionalSecondPSD {H : ℕ → Type*} (history : (k : ℕ) → Ω → H k) (k : ℕ)
    (p : Ω → ℝ) (E : Ω → Mat m n) (Ψ : Mat n n →ₗ[ℝ] Mat m m) : Prop :=
  ∀ T : Ω → Mat n n, Past history k T → (∀ ω,(T ω).PosSemidef) →
    mean p (fun ω => E ω*T ω*(E ω).transpose)=Ψ (mean p T)

theorem secondPSD_operator_positive {H : ℕ → Type*} (history : (k : ℕ) → Ω → H k)
    (k : ℕ) (p : Ω → ℝ) (E : Ω → Mat m n) (Ψ : Mat n n →ₗ[ℝ] Mat m m)
    (law : FiniteLaw p) (hsecond : ConditionalSecondPSD history k p E Ψ)
    (T : Mat n n) (hT : T.PosSemidef) : (Ψ T).PosSemidef := by
  have hpast : Past history k (fun _ : Ω => T) := by intro ω η h; rfl
  have hh := hsecond (fun _ => T) hpast (fun _ => hT)
  rw [mean_const p T law.mass] at hh
  rw [← hh]
  apply mean_posSemidef p _ law.nonnegative
  intro ω
  simpa using hT.mul_mul_conjTranspose_same (E ω)

theorem mean_congruence (p : Ω → ℝ) (W : Mat m n) (A : Ω → Mat n t) :
    mean p (fun ω => (W*A ω)*(W*A ω).transpose)=
      W*mean p (fun ω => A ω*(A ω).transpose)*W.transpose := by
  calc
    _ = mean p (fun ω => (W*(A ω*(A ω).transpose))*W.transpose) := by
      apply congrArg (mean p)
      funext ω
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = _ := by rw [mean_mul_const,mean_const_mul]



theorem affine_actual_second_moment {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (Z : Ω → Mat n t) (A : Ω → Mat m t)
    (Ψ : Mat n n →ₗ[ℝ] Mat m m)
    (hZpast : Past history k Z) (hApast : Past history k A)
    (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ) :
    mean p (fun ω => (A ω+E ω*Z ω)*(A ω+E ω*Z ω).transpose)=
      mean p (fun ω => A ω*(A ω).transpose)+Ψ (mean p (fun ω => Z ω*(Z ω).transpose)) := by
  let N := fun ω => E ω*Z ω
  have hAZpast : Past history k (fun ω => A ω*(Z ω).transpose) :=
    past_map history k (fun ω => (A ω,Z ω)) (fun z => z.1*z.2.transpose)
      (past_pair history k A Z hApast hZpast)
  have hcross : mean p (fun ω => A ω*(N ω).transpose)=0 := by
    have hh := mean_past_mul_noise_transpose_zero history k p E
      (fun ω => A ω*(Z ω).transpose) hAZpast hfirst
    simpa only [N,Matrix.transpose_mul,Matrix.mul_assoc] using hh
  have hcrossT : mean p (fun ω => N ω*(A ω).transpose)=0 := by
    have hh := congrArg Matrix.transpose hcross
    rw [← mean_transpose] at hh
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using hh
  have hN : mean p (fun ω => N ω*(N ω).transpose)=
      Ψ (mean p (fun ω => Z ω*(Z ω).transpose)) := by
    have hh := hsecond (fun ω => Z ω*(Z ω).transpose)
      (past_map history k Z (fun M => M*M.transpose) hZpast)
      (fun ω => by simpa using Matrix.posSemidef_self_mul_conjTranspose (Z ω))
    simpa only [N,Matrix.transpose_mul,Matrix.mul_assoc] using hh
  change mean p (fun ω => (A ω+N ω)*(A ω+N ω).transpose)=_
  simp only [Matrix.transpose_add,Matrix.add_mul,Matrix.mul_add,mean_add,
    hcross,hcrossT,hN,add_zero,zero_add]

variable {H : ℕ → Type*} (history : (k : ℕ) → Ω → H k) (k : ℕ)
variable (p : Ω → ℝ) (E : Ω → Mat m n) (Z : Ω → Mat n t)
variable (W : Mat m n) (X : Mat n t) (a : ℝ)
variable (Ψ : Mat n n →ₗ[ℝ] Mat m m)


theorem actual_qep_output_moment
    (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → IsUnit (gram (Z ω)).det) :
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
    (hgram : ∀ ω,p ω ≠ 0 → IsUnit (gram (Z ω)).det) :
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


theorem actual_base_mean (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E) :
    mean p (fun ω => (W+E ω)*Z ω)=W*mean p Z := by
  simp only [Matrix.add_mul,mean_add,mean_const_mul,
    mean_noise_mul_zero history k p E Z hZpast hfirst,add_zero]

theorem actual_base_output_moment (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ) :
    mean p (fun ω => ((W+E ω)*Z ω)*((W+E ω)*Z ω).transpose)=
      W*mean p (fun ω => Z ω*(Z ω).transpose)*W.transpose+
      Ψ (mean p (fun ω => Z ω*(Z ω).transpose)) := by
  have hh := affine_actual_second_moment history k p E Z (fun ω => W*Z ω) Ψ hZpast
    (past_map history k Z (fun M => W*M) hZpast) hfirst hsecond
  rw [mean_congruence] at hh
  simpa only [Matrix.add_mul] using hh

theorem actual_base_error_moment (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ) :
    mean p (fun ω => ((W+E ω)*Z ω-W*X)*((W+E ω)*Z ω-W*X).transpose)=
      W*mean p (fun ω => (Z ω-X)*(Z ω-X).transpose)*W.transpose+
      Ψ (mean p (fun ω => Z ω*(Z ω).transpose)) := by
  have he (ω : Ω) : (W+E ω)*Z ω-W*X=W*(Z ω-X)+E ω*Z ω := by
    simp only [Matrix.add_mul,Matrix.mul_sub]; abel
  simp only [he]
  rw [affine_actual_second_moment history k p E Z (fun ω => W*(Z ω-X)) Ψ hZpast
    (past_map history k Z (fun M => W*(M-X)) hZpast) hfirst hsecond,mean_congruence]

end
end QepX1
