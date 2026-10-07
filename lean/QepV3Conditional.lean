import QepV3Expectation

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV3
noncomputable section
open QepCorrected QepGram
open scoped BigOperators
variable {Ω m n t : Type*} [Fintype Ω] [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]


theorem gram_smul_add (D N : Mat m t) (a : ℝ) :
    (a • D+N)*(a • D+N).transpose =
      a^2 • (D*D.transpose)+a • (D*N.transpose)+a • (N*D.transpose)+N*N.transpose := by
  simp only [Matrix.transpose_add,Matrix.transpose_smul,Matrix.add_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,smul_add,smul_smul,pow_two]
  abel

variable {H : ℕ → Type*} (history : (k : ℕ) → Ω → H k) (k : ℕ)
variable (p : Ω → ℝ) (E : Ω → Mat m n) (Z : Ω → Mat n t)
variable (W : Mat m n) (X : Mat n t) (a : ℝ)
variable (Ψ : Mat n n →ₗ[ℝ] Mat m m)


def ConditionalMeanZero : Prop :=
  ∀ f : Ω → ℝ, Past history k f → ∀ i j, (∑ ω,p ω*(f ω*E ω i j))=0



def ConditionalSecondOperator : Prop :=
  ∀ T : Ω → Mat n n, Past history k T →
    mean p (fun ω => E ω*T ω*(E ω).transpose)=Ψ (mean p T)


theorem actual_layer_mean
    (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hgram : ∀ ω,p ω ≠ 0 → IsUnit (gram (Z ω)).det)
    (hrow : ∀ ω,p ω ≠ 0 → X*gramProjection (Z ω)=X) :
    mean p (fun ω => (correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)=
      (1-a) • (W*mean p (fun ω => Z ω-X)) := by
  have he : mean p (fun ω => (correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)=
      mean p (fun ω => (1-a) • (W*(Z ω-X))+E ω*Z ω) := by
    apply mean_support_congr
    intro ω hω
    exact actual_error_step W (E ω) X (Z ω) a (hgram ω hω) (hrow ω hω)
  rw [he,mean_add,mean_smul,mean_const_mul,
    mean_noise_mul_zero history k p E Z hZpast hfirst,add_zero]



theorem conditional_operator_positive (law : FiniteLaw p)
    (hsecond : ConditionalSecondOperator history k p E Ψ)
    (T : Mat n n) (hT : T.PosSemidef) : (Ψ T).PosSemidef := by
  have hpast : Past history k (fun _ : Ω => T) := by intro ω η h; rfl
  have hh := hsecond (fun _ => T) hpast
  rw [mean_const p T law.mass] at hh
  rw [← hh]
  apply mean_posSemidef p _ law.nonnegative
  intro ω
  simpa using hT.mul_mul_conjTranspose_same (E ω)



theorem actual_layer_second_moment (law : FiniteLaw p)
    (hZpast : Past history k Z)
    (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondOperator history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → IsUnit (gram (Z ω)).det)
    (hrow : ∀ ω,p ω ≠ 0 → X*gramProjection (Z ω)=X)
    (hmean : mean p (fun ω => Z ω-X)=0) :
    mean p (fun ω =>
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X).transpose) =
      (1-a)^2 • (W*mean p (fun ω => (Z ω-X)*(Z ω-X).transpose)*W.transpose)+
      Ψ (mean p (fun ω => (Z ω-X)*(Z ω-X).transpose)+X*X.transpose) := by
  let R := fun ω => Z ω-X
  let D := fun ω => W*R ω
  let N := fun ω => E ω*Z ω
  have hDpast : Past history k D := past_map history k Z (fun M => W*(M-X)) hZpast
  have hAZpast : Past history k (fun ω => D ω*(Z ω).transpose) :=
    past_map history k (fun ω => (D ω,Z ω)) (fun z => z.1*z.2.transpose)
      (past_pair history k D Z hDpast hZpast)
  have hcross : mean p (fun ω => D ω*(N ω).transpose)=0 := by
    have hh := mean_past_mul_noise_transpose_zero history k p E
      (fun ω => D ω*(Z ω).transpose) hAZpast hfirst
    simpa only [N,Matrix.transpose_mul,Matrix.mul_assoc] using hh
  have hcrossT : mean p (fun ω => N ω*(D ω).transpose)=0 := by
    have hh := congrArg Matrix.transpose hcross
    rw [← mean_transpose] at hh
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using hh
  have hN : mean p (fun ω => N ω*(N ω).transpose)=
      Ψ (mean p (fun ω => Z ω*(Z ω).transpose)) := by
    have hh := hsecond (fun ω => Z ω*(Z ω).transpose)
      (past_map history k Z (fun M => M*M.transpose) hZpast)
    simpa only [N,Matrix.transpose_mul,Matrix.mul_assoc] using hh
  have hinput : mean p (fun ω => Z ω*(Z ω).transpose)=
      mean p (fun ω => R ω*(R ω).transpose)+X*X.transpose := by
    have hh := mean_shifted_gram p R X law.mass hmean
    simpa only [R,sub_add_cancel] using hh
  have hD : mean p (fun ω => D ω*(D ω).transpose)=
      W*mean p (fun ω => R ω*(R ω).transpose)*W.transpose := by
    calc
      _ = mean p (fun ω => (W*(R ω*(R ω).transpose))*W.transpose) := by
        apply congrArg (mean p)
        funext ω
        simp only [D,Matrix.transpose_mul,Matrix.mul_assoc]
      _ = _ := by rw [mean_mul_const,mean_const_mul]
  have he : mean p (fun ω =>
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X).transpose)=
      mean p (fun ω => ((1-a) • D ω+N ω)*((1-a) • D ω+N ω).transpose) := by
    apply mean_support_congr
    intro ω hω
    rw [actual_error_step W (E ω) X (Z ω) a (hgram ω hω) (hrow ω hω)]
  rw [he]
  simp only [gram_smul_add,mean_add,mean_smul,hcross,hcrossT,smul_zero,add_zero,hD,hN,hinput,R]

end
end QepV3
