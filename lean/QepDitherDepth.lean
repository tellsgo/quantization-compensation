import QepDitherFinite
import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace QepDitherDepth
noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω]

def expect (p f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

def Past (e : ℕ → Ω → ℝ) (n : ℕ) (f : Ω → ℝ) : Prop :=
  ∀ ω η, (∀ k, k < n → e k ω = e k η) → f ω = f η



structure ConditionalMoments (p : Ω → ℝ) (e : ℕ → Ω → ℝ)
    (v : ℕ → ℝ) (L : ℕ) : Prop where
  first : ∀ n, n < L → ∀ f, Past e n f → expect p (fun ω => f ω * e n ω) = 0
  second : ∀ n, n < L → ∀ f, Past e n f →
    expect p (fun ω => f ω * (e n ω)^2) = v n * expect p f

def teacher (w : ℕ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => w n * teacher w x n

def student (w alpha : ℕ → ℝ) (x : ℝ) (e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x
  | n+1 => fun ω =>
      (QepSharedE.corrected (alpha n) (w n) (teacher w x n)
        (student w alpha x e n ω) + e n ω) * student w alpha x e n ω

def error (w alpha : ℕ → ℝ) (x : ℝ) (e : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => student w alpha x e n ω - teacher w x n

def mse (p : Ω → ℝ) (w alpha : ℕ → ℝ) (x : ℝ) (e : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  expect p (fun ω => (error w alpha x e n ω)^2)

def Legal (p : Ω → ℝ) (w alpha : ℕ → ℝ) (x : ℝ) (e : ℕ → Ω → ℝ) (L : ℕ) : Prop :=
  ∀ n, n < L → ∀ ω, p ω ≠ 0 → student w alpha x e n ω ≠ 0

theorem scalar_step (a w x z e : ℝ) (hz : z ≠ 0) :
    (QepSharedE.corrected a w x z + e)*z-w*x = (1-a)*w*(z-x)+e*z := by
  unfold QepSharedE.corrected QepSharedE.gram
  field_simp
  ring

theorem past_student (w alpha : ℕ → ℝ) (x : ℝ) (e : ℕ → Ω → ℝ) (n : ℕ) :
    Past e n (student w alpha x e n) := by
  induction n with
  | zero => intro ω η h; rfl
  | succ n ih =>
    intro ω η h
    have hn : student w alpha x e n ω = student w alpha x e n η :=
      ih ω η (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    simp only [student, hn, h n (Nat.lt_succ_self n)]

theorem past_error (w alpha : ℕ → ℝ) (x : ℝ) (e : ℕ → Ω → ℝ) (n : ℕ) :
    Past e n (error w alpha x e n) := by
  intro ω η h
  unfold error
  rw [past_student w alpha x e n ω η h]

theorem past_mul (e : ℕ → Ω → ℝ) (n : ℕ) (f g : Ω → ℝ)
    (hf : Past e n f) (hg : Past e n g) : Past e n (fun ω => f ω*g ω) := by
  intro ω η h
  change f ω*g ω = f η*g η
  rw [hf ω η h, hg ω η h]

theorem past_sq (e : ℕ → Ω → ℝ) (n : ℕ) (f : Ω → ℝ)
    (hf : Past e n f) : Past e n (fun ω => (f ω)^2) := by
  intro ω η h
  change (f ω)^2 = (f η)^2
  rw [hf ω η h]

theorem expect_support_congr (p f g : Ω → ℝ)
    (h : ∀ ω, p ω ≠ 0 → f ω = g ω) : expect p f = expect p g := by
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hp : p ω = 0
  · simp [hp]
  · rw [h ω hp]

theorem expect_add (p f g : Ω → ℝ) :
    expect p (fun ω => f ω+g ω) = expect p f+expect p g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_cmul (p f : Ω → ℝ) (c : ℝ) :
    expect p (fun ω => c*f ω) = c*expect p f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_const (p : Ω → ℝ) (c : ℝ) (hp : ∑ ω,p ω = 1) :
    expect p (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul,hp,one_mul]

theorem actual_error_step (p : Ω → ℝ) (w alpha : ℕ → ℝ) (x : ℝ)
    (e : ℕ → Ω → ℝ) (L n : ℕ) (hl : Legal p w alpha x e L)
    (hn : n < L) (ω : Ω) (hp : p ω ≠ 0) :
    error w alpha x e (n+1) ω =
      (1-alpha n)*w n*error w alpha x e n ω + e n ω*student w alpha x e n ω := by
  exact scalar_step (alpha n) (w n) (teacher w x n) (student w alpha x e n ω)
    (e n ω) (hl n hn ω hp)

theorem actual_mean_zero (p : Ω → ℝ) (w alpha v : ℕ → ℝ) (x : ℝ)
    (e : ℕ → Ω → ℝ) (L : ℕ) (hl : Legal p w alpha x e L)
    (hm : ConditionalMoments p e v L) (n : ℕ) (hn : n ≤ L) :
    expect p (error w alpha x e n) = 0 := by
  induction n with
  | zero => simp [error,student,teacher,expect]
  | succ n ih =>
    have hnL : n < L := by omega
    have H : expect p (error w alpha x e (n+1)) =
        expect p (fun ω => ((1-alpha n)*w n)*error w alpha x e n ω +
          student w alpha x e n ω*e n ω) := by
      apply expect_support_congr
      intro ω hp
      rw [actual_error_step p w alpha x e L n hl hnL ω hp]
      ring
    rw [H,expect_add,expect_cmul,ih (by omega),mul_zero,zero_add]
    exact hm.first n hnL _ (past_student w alpha x e n)

theorem actual_mse_step (p : Ω → ℝ) (w alpha v : ℕ → ℝ) (x : ℝ)
    (e : ℕ → Ω → ℝ) (L : ℕ) (hp : ∑ ω,p ω = 1)
    (hl : Legal p w alpha x e L) (hm : ConditionalMoments p e v L)
    (n : ℕ) (hn : n < L) :
    mse p w alpha x e (n+1) =
      ((1-alpha n)^2*(w n)^2+v n)*mse p w alpha x e n + v n*(teacher w x n)^2 := by
  let r := error w alpha x e n
  let z := student w alpha x e n
  have hr : Past e n r := past_error w alpha x e n
  have hz : Past e n z := past_student w alpha x e n
  have hzero : expect p r = 0 := actual_mean_zero p w alpha v x e L hl hm n (by omega)
  have hzsq : expect p (fun ω => (z ω)^2) = (teacher w x n)^2 + mse p w alpha x e n := by
    have heq : expect p (fun ω => (z ω)^2) =
      expect p (fun _ => (teacher w x n)^2) +
      (2*teacher w x n)*expect p r + expect p (fun ω => (r ω)^2) := by
      rw [← expect_cmul,← expect_add,← expect_add]
      apply expect_support_congr
      intro ω _
      dsimp [r,z,error]
      ring
    rw [heq,expect_const p _ hp,hzero,mul_zero,add_zero]
    rfl
  have hcross := hm.first n hn (fun ω => r ω*z ω) (past_mul e n r z hr hz)
  have hsecond := hm.second n hn (fun ω => (z ω)^2) (past_sq e n z hz)
  have heq : mse p w alpha x e (n+1) =
      ((1-alpha n)^2*(w n)^2)*expect p (fun ω => (r ω)^2) +
      (2*(1-alpha n)*w n)*expect p (fun ω => (r ω*z ω)*e n ω) +
      expect p (fun ω => (z ω)^2*(e n ω)^2) := by
    rw [← expect_cmul,← expect_cmul,← expect_add,← expect_add]
    apply expect_support_congr
    intro ω hω
    rw [actual_error_step p w alpha x e L n hl hn ω hω]
    dsimp [r,z]
    ring
  rw [heq,hcross,mul_zero,add_zero,hsecond,hzsq]
  change ((1-alpha n)^2*(w n)^2)*mse p w alpha x e n +
    v n*((teacher w x n)^2+mse p w alpha x e n) = _
  ring


def moment (w alpha v : ℕ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => ((1-alpha n)^2*(w n)^2+v n)*moment w alpha v x n + v n*(teacher w x n)^2

theorem actual_mse_eq_moment (p : Ω → ℝ) (w alpha v : ℕ → ℝ) (x : ℝ)
    (e : ℕ → Ω → ℝ) (L : ℕ) (hp : ∑ ω,p ω = 1)
    (hl : Legal p w alpha x e L) (hm : ConditionalMoments p e v L)
    (n : ℕ) (hn : n ≤ L) : mse p w alpha x e n = moment w alpha v x n := by
  induction n with
  | zero => simp [mse,error,student,teacher,expect,moment]
  | succ n ih =>
    rw [actual_mse_step p w alpha v x e L hp hl hm n (by omega),ih (by omega)]
    rfl

theorem moment_nonnegative (w alpha v : ℕ → ℝ) (x : ℝ)
    (hv : ∀ n,0 ≤ v n) (n : ℕ) : 0 ≤ moment w alpha v x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [moment]
    have hvn := hv n
    positivity

theorem moment_antitone (w a b v : ℕ → ℝ) (x : ℝ)
    (hv : ∀ n,0 ≤ v n) (ha : ∀ n,0 ≤ a n) (hab : ∀ n,a n ≤ b n)
    (hb : ∀ n,b n ≤ 1) (n : ℕ) : moment w b v x n ≤ moment w a v x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hsq : (1-b n)^2 ≤ (1-a n)^2 := by nlinarith [ha n,hab n,hb n]
    have hcoef : (1-b n)^2*(w n)^2+v n ≤ (1-a n)^2*(w n)^2+v n := by
      nlinarith [sq_nonneg (w n),mul_le_mul_of_nonneg_right hsq (sq_nonneg (w n))]
    have hz := moment_nonnegative w b v x hv n
    have hvn := hv n
    have hp : 0 ≤ (1-a n)^2*(w n)^2+v n := by positivity
    simpa only [moment] using add_le_add (mul_le_mul hcoef ih hz hp)
      (le_refl (v n*(teacher w x n)^2))

theorem actual_mse_antitone (p : Ω → ℝ) (w a b v : ℕ → ℝ) (x : ℝ)
    (ea eb : ℕ → Ω → ℝ) (L : ℕ) (hp : ∑ ω,p ω = 1)
    (hla : Legal p w a x ea L) (hlb : Legal p w b x eb L)
    (hma : ConditionalMoments p ea v L) (hmb : ConditionalMoments p eb v L)
    (hv : ∀ n,0 ≤ v n) (ha : ∀ n,0 ≤ a n) (hab : ∀ n,a n ≤ b n)
    (hb : ∀ n,b n ≤ 1) : mse p w b x eb L ≤ mse p w a x ea L := by
  rw [actual_mse_eq_moment p w b v x eb L hp hlb hmb L (le_refl L),
    actual_mse_eq_moment p w a v x ea L hp hla hma L (le_refl L)]
  exact moment_antitone w a b v x hv ha hab hb L

theorem student_two_eq_existing (w alpha : ℕ → ℝ) (x : ℝ)
    (e : ℕ → Ω → ℝ) (ω : Ω) :
    student w alpha x e 2 ω =
      (QepSharedE.qepTrace ⟨w 0,w 1,x,1,1⟩ ⟨e 0 ω,e 1 ω⟩ (alpha 0) (alpha 1)).output := by
  rfl

theorem two_layer_equal_variance (w alpha : ℕ → ℝ) (x s : ℝ) :
    moment w alpha (fun _ => s) x 2 =
      x^2*s*((1-alpha 1)^2*(w 1)^2+(w 0)^2+s) := by
  simp only [moment,teacher]
  ring

structure FiniteLaw (p : Ω → ℝ) : Prop where
  nonnegative : ∀ ω,0 ≤ p ω
  mass : ∑ ω,p ω = 1

def coefficient (w alpha v : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1-alpha n)^2*(w n)^2+v n

theorem moment_sum_product (w alpha v : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    moment w alpha v x n =
      ∑ k ∈ Finset.range n, v k*(teacher w x k)^2*
        ∏ j ∈ Finset.Ico (k+1) n, coefficient w alpha v j := by
  induction n with
  | zero => simp [moment]
  | succ n ih =>
    rw [moment,ih,Finset.sum_range_succ]
    simp only [Finset.Ico_self,Finset.prod_empty,mul_one]
    apply congrArg (fun y : ℝ => y+v n*(teacher w x n)^2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_Ico_succ_top (by have := Finset.mem_range.mp hk; omega)]
    unfold coefficient
    ring

theorem finite_law_actual_closed_form (p : Ω → ℝ) (w alpha v : ℕ → ℝ) (x : ℝ)
    (e : ℕ → Ω → ℝ) (L : ℕ) (law : FiniteLaw p)
    (hl : Legal p w alpha x e L) (hm : ConditionalMoments p e v L) :
    mse p w alpha x e L =
      ∑ k ∈ Finset.range L, v k*(teacher w x k)^2*
        ∏ j ∈ Finset.Ico (k+1) L, coefficient w alpha v j := by
  rw [actual_mse_eq_moment p w alpha v x e L law.mass hl hm L (le_refl L)]
  exact moment_sum_product w alpha v x L

theorem finite_law_actual_mse_comparison (p : Ω → ℝ) (w a b v : ℕ → ℝ) (x : ℝ)
    (ea eb : ℕ → Ω → ℝ) (L : ℕ) (law : FiniteLaw p)
    (hla : Legal p w a x ea L) (hlb : Legal p w b x eb L)
    (hma : ConditionalMoments p ea v L) (hmb : ConditionalMoments p eb v L)
    (hv : ∀ n,0 ≤ v n) (ha : ∀ n,0 ≤ a n) (hab : ∀ n,a n ≤ b n)
    (hb : ∀ n,b n ≤ 1) : mse p w b x eb L ≤ mse p w a x ea L := by
  exact actual_mse_antitone p w a b v x ea eb L law.mass hla hlb hma hmb hv ha hab hb


end
end QepDitherDepth
