import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

namespace QepSharedE
noncomputable section



def activation (x : ℝ) : ℝ := x
def gram (x : ℝ) : ℝ := x^2
structure Network where
  w1 : ℝ
  w2 : ℝ
  input : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
structure Errors where
  e1 : ℝ
  e2 : ℝ
structure Trace where
  target1 : ℝ
  target2 : ℝ
  weight1 : ℝ
  weight2 : ℝ
  input1 : ℝ
  input2 : ℝ
  output : ℝ

def teacher2 (n : Network) : ℝ := activation (n.w1*n.input)
def teacherOutput (n : Network) : ℝ := activation (n.w2*teacher2 n)

def corrected (alpha w x y : ℝ) : ℝ :=
  w + alpha*w*(x-y)*y/gram y

def baseTrace (n : Network) (e : Errors) : Trace :=
  let q1 := n.w1+e.e1
  let x2 := activation (q1*n.input)
  let q2 := n.w2+e.e2
  ⟨n.w1,n.w2,q1,q2,n.input,x2,activation (q2*x2)⟩
def qepTrace (n : Network) (e : Errors) (alpha1 alpha2 : ℝ) : Trace :=
  let s1 := corrected alpha1 n.w1 n.input n.input
  let q1 := s1+e.e1
  let x2 := activation (q1*n.input)
  let s2 := corrected alpha2 n.w2 (teacher2 n) x2
  let q2 := s2+e.e2
  ⟨s1,s2,q1,q2,n.input,x2,activation (q2*x2)⟩


def residual1 (n : Network) (t : Trace) : ℝ := n.w1*n.input-t.weight1*t.input1
def residual2 (n : Network) (t : Trace) : ℝ := n.w2*teacher2 n-t.weight2*t.input2

def upper (n : Network) (t : Trace) : ℝ :=
  n.gamma1 * n.gamma2 * |n.w2| * |residual1 n t| + n.gamma2 * |residual2 n t|
def terminalError (n : Network) (t : Trace) : ℝ := |teacherOutput n-t.output|


def fixed : Network := ⟨1,1,1,1,1⟩
def noise (epsilon : ℝ) : Errors := ⟨epsilon,-epsilon⟩
def controlNoise (epsilon : ℝ) : Errors := ⟨epsilon,epsilon⟩
def baseRun (epsilon : ℝ) : Trace := baseTrace fixed (noise epsilon)
def qepRun (epsilon : ℝ) : Trace := qepTrace fixed (noise epsilon) 1 1
def baseU (epsilon : ℝ) : ℝ := upper fixed (baseRun epsilon)
def qepU (epsilon : ℝ) : ℝ := upper fixed (qepRun epsilon)
def baseErr (epsilon : ℝ) : ℝ := terminalError fixed (baseRun epsilon)
def qepErr (epsilon : ℝ) : ℝ := terminalError fixed (qepRun epsilon)
def noiseNorm (e : Errors) : ℝ := max |e.e1| |e.e2|

theorem identity_lipschitz : activation 0 = 0 ∧
    ∀ x y : ℝ, |activation x-activation y| ≤ 1*|x-y| := by
  simp [activation]

theorem recover_shared_errors (n : Network) (e : Errors) (a1 a2 : ℝ) :
    (baseTrace n e).weight1-(baseTrace n e).target1 = e.e1 ∧
    (baseTrace n e).weight2-(baseTrace n e).target2 = e.e2 ∧
    (qepTrace n e a1 a2).weight1-(qepTrace n e a1 a2).target1 = e.e1 ∧
    (qepTrace n e a1 a2).weight2-(qepTrace n e a1 a2).target2 = e.e2 := by
  simp [baseTrace,qepTrace]

theorem corrected_unit {y : ℝ} (hy : y ≠ 0) : corrected 1 1 1 y = 1/y := by
  unfold corrected gram
  field_simp
  <;> ring

theorem base_closed (epsilon : ℝ) :
    baseRun epsilon = ⟨1,1,1+epsilon,1-epsilon,1,1+epsilon,1-epsilon^2⟩ := by
  simp only [baseRun,baseTrace,fixed,noise,activation]
  congr 1 <;> ring

theorem qep_closed {epsilon : ℝ} (he : 0 < epsilon) :
    qepRun epsilon = ⟨1,1/(1+epsilon),1+epsilon,1/(1+epsilon)-epsilon,
      1,1+epsilon,1-epsilon-epsilon^2⟩ := by
  have hd : 1+epsilon ≠ 0 := by linarith
  have hs : corrected 1 1 1 1 = 1 := by norm_num [corrected,gram]
  simp only [qepRun,qepTrace,fixed,noise,teacher2,activation,mul_one,hs]
  rw [corrected_unit hd]
  congr 1 <;> field_simp <;> ring

theorem exact_residuals {epsilon : ℝ} (he : 0 < epsilon) :
    residual1 fixed (baseRun epsilon) = -epsilon ∧
    residual1 fixed (qepRun epsilon) = -epsilon ∧
    residual2 fixed (baseRun epsilon) = epsilon^2 ∧
    residual2 fixed (qepRun epsilon) = epsilon+epsilon^2 := by
  rw [base_closed,qep_closed he]
  simp only [residual1,residual2,fixed,teacher2,activation,mul_one]
  have hd : 1+epsilon ≠ 0 := by linarith
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · field_simp
    <;> ring

theorem exact_errors {epsilon : ℝ} (he : 0 < epsilon) :
    baseU epsilon = epsilon+epsilon^2 ∧ qepU epsilon = 2*epsilon+epsilon^2 ∧
    baseErr epsilon = epsilon^2 ∧ qepErr epsilon = epsilon+epsilon^2 := by
  obtain ⟨hb1,hq1,hb2,hq2⟩ := exact_residuals he
  have hsq : 0 ≤ epsilon^2 := sq_nonneg _
  have hs : 0 ≤ epsilon+epsilon^2 := by positivity
  have ha : |(-epsilon)| = epsilon := by rw [abs_neg,abs_of_pos he]
  constructor
  · rw [baseU,upper,hb1,hb2]
    norm_num [fixed,ha,abs_of_nonneg hsq]
  constructor
  · rw [qepU,upper,hq1,hq2]
    norm_num [fixed,ha,abs_of_nonneg hs]
    ring
  constructor
  · rw [baseErr,terminalError,base_closed]
    simp [teacherOutput,teacher2,activation,fixed,abs_of_nonneg hsq]
  · rw [qepErr,terminalError,qep_closed he]
    have hh : (1:ℝ)-(1-epsilon-epsilon^2) = epsilon+epsilon^2 := by ring
    simp only [teacherOutput,teacher2,activation,fixed,mul_one,hh]
    exact abs_of_nonneg hs

structure Legal (epsilon : ℝ) : Prop where
  identity_conditions : activation 0 = 0 ∧ ∀ x y : ℝ, |activation x-activation y| ≤ 1*|x-y|
  alpha_conditions : (0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1
  teacher_nonzero : fixed.w1 ≠ 0 ∧ fixed.w2 ≠ 0
  weight_positive : 0 < (baseRun epsilon).weight1 ∧ 0 < (baseRun epsilon).weight2 ∧
    0 < (qepRun epsilon).weight1 ∧ 0 < (qepRun epsilon).weight2
  gram_positive : 0 < gram fixed.input ∧ 0 < gram (teacher2 fixed) ∧
    0 < gram (baseRun epsilon).input1 ∧ 0 < gram (baseRun epsilon).input2 ∧
    0 < gram (qepRun epsilon).input1 ∧ 0 < gram (qepRun epsilon).input2

theorem legal {epsilon : ℝ} (he : 0 < epsilon) (hu : epsilon < 1/2) : Legal epsilon := by
  have hd : 0 < 1+epsilon := by linarith
  have hq : 0 < 1/(1+epsilon)-epsilon := by
    have hh : epsilon*(1+epsilon) < 1 := by
      have hsq : epsilon^2 < 1/4 := by nlinarith
      nlinarith
    have hr : epsilon < 1/(1+epsilon) := (lt_div_iff₀ hd).mpr hh
    linarith
  refine ⟨identity_lipschitz,by norm_num,by norm_num [fixed],?_,?_⟩
  · rw [base_closed,qep_closed he]
    dsimp
    exact ⟨hd,by linarith,hd,hq⟩
  · rw [base_closed,qep_closed he]
    norm_num [gram,fixed,teacher2,activation]
    positivity


theorem core {epsilon : ℝ} (he : 0 < epsilon) (hu : epsilon < 1/2) :
    Legal epsilon ∧
    baseRun epsilon = ⟨1,1,1+epsilon,1-epsilon,1,1+epsilon,1-epsilon^2⟩ ∧
    qepRun epsilon = ⟨1,1/(1+epsilon),1+epsilon,1/(1+epsilon)-epsilon,
      1,1+epsilon,1-epsilon-epsilon^2⟩ ∧
    residual1 fixed (baseRun epsilon) = -epsilon ∧
    residual1 fixed (qepRun epsilon) = -epsilon ∧
    residual2 fixed (baseRun epsilon) = epsilon^2 ∧
    residual2 fixed (qepRun epsilon) = epsilon+epsilon^2 ∧
    qepU epsilon-baseU epsilon = epsilon ∧ baseU epsilon < qepU epsilon ∧
    baseErr epsilon = epsilon^2 ∧ qepErr epsilon = epsilon+epsilon^2 ∧
    baseErr epsilon < qepErr epsilon := by
  obtain ⟨hb1,hq1,hb2,hq2⟩ := exact_residuals he
  obtain ⟨hbU,hqU,hbE,hqE⟩ := exact_errors he
  refine ⟨legal he hu,base_closed epsilon,qep_closed he,hb1,hq1,hb2,hq2,?_,?_,hbE,hqE,?_⟩
  · rw [hbU,hqU]; ring
  · rw [hbU,hqU]; linarith
  · rw [hbE,hqE]; linarith



theorem first_order {epsilon : ℝ} (he : 0 < epsilon) :
    noiseNorm (noise epsilon) = epsilon ∧
    |baseU epsilon-epsilon| = epsilon^2 ∧
    |qepU epsilon-2*epsilon| = epsilon^2 ∧
    |baseErr epsilon-0| = epsilon^2 ∧
    |qepErr epsilon-epsilon| = epsilon^2 ∧
    (qepU epsilon-baseU epsilon)/epsilon = 1 := by
  obtain ⟨hb,hq,heb,heq⟩ := exact_errors he
  rw [hb,hq,heb,heq]
  have hsq : 0 ≤ epsilon^2 := sq_nonneg _
  have hdiv : (2*epsilon+epsilon^2-(epsilon+epsilon^2))/epsilon = 1 := by
    field_simp
    <;> ring
  refine ⟨?_,?_,?_,?_,?_,hdiv⟩
  · simp [noiseNorm,noise,abs_of_pos he]
  · simpa only [add_sub_cancel_left] using abs_of_nonneg hsq
  · simpa only [add_sub_cancel_left] using abs_of_nonneg hsq
  · simpa only [sub_zero] using abs_of_nonneg hsq
  · simpa only [add_sub_cancel_left] using abs_of_nonneg hsq

theorem arbitrarily_small (eta : ℝ) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < min eta (1/2) ∧
    Legal epsilon ∧ noiseNorm (noise epsilon) = epsilon ∧
    qepU epsilon-baseU epsilon = epsilon ∧ baseU epsilon < qepU epsilon ∧
    baseErr epsilon = epsilon^2 ∧ qepErr epsilon = epsilon+epsilon^2 ∧
    |baseU epsilon-epsilon| ≤ epsilon^2 ∧ |qepU epsilon-2*epsilon| ≤ epsilon^2 := by
  let epsilon : ℝ := min eta (1/2)/2
  have hm : 0 < min eta (1/2 : ℝ) := lt_min heta (by norm_num)
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  have hsmall : epsilon < min eta (1/2) := by dsimp [epsilon]; linarith
  have hu : epsilon < 1/2 := lt_of_lt_of_le hsmall (min_le_right _ _)
  obtain ⟨hb,hq,heb,heq⟩ := exact_errors he
  obtain ⟨hn,hbr,hqr,_,_,_⟩ := first_order he
  refine ⟨epsilon,he,hsmall,legal he hu,hn,?_,?_,heb,heq,le_of_eq hbr,le_of_eq hqr⟩
  · rw [hb,hq]; ring
  · rw [hb,hq]; linarith



theorem same_input_cancellation {epsilon : ℝ} (he : 0 < epsilon) :
    (baseRun epsilon).input2 = (qepRun epsilon).input2 ∧
    fixed.w2 * (teacher2 fixed-(qepRun epsilon).input2) = -epsilon ∧
    (noise epsilon).e2 * (qepRun epsilon).input2 = -epsilon-epsilon^2 ∧
    |residual2 fixed (baseRun epsilon)| < |residual2 fixed (qepRun epsilon)| := by
  obtain ⟨_,_,hb,hq⟩ := exact_residuals he
  rw [hb,hq,base_closed,qep_closed he]
  norm_num [fixed,teacher2,activation,noise,abs_of_nonneg (sq_nonneg epsilon),
    abs_of_pos (show 0 < epsilon+epsilon^2 by positivity)]
  constructor
  · ring
  · exact he


def controlBase (epsilon : ℝ) : Trace := baseTrace fixed (controlNoise epsilon)
def controlQep (epsilon : ℝ) : Trace := qepTrace fixed (controlNoise epsilon) 1 1
def controlBaseU (epsilon : ℝ) : ℝ := upper fixed (controlBase epsilon)
def controlQepU (epsilon : ℝ) : ℝ := upper fixed (controlQep epsilon)
def controlBaseErr (epsilon : ℝ) : ℝ := terminalError fixed (controlBase epsilon)
def controlQepErr (epsilon : ℝ) : ℝ := terminalError fixed (controlQep epsilon)

theorem control_closed {epsilon : ℝ} (he : 0 < epsilon) :
    controlBase epsilon = ⟨1,1,1+epsilon,1+epsilon,1,1+epsilon,1+2*epsilon+epsilon^2⟩ ∧
    controlQep epsilon = ⟨1,1/(1+epsilon),1+epsilon,1/(1+epsilon)+epsilon,
      1,1+epsilon,1+epsilon+epsilon^2⟩ := by
  constructor
  · simp only [controlBase,baseTrace,fixed,controlNoise,activation]
    congr 1 <;> ring
  · have hd : 1+epsilon ≠ 0 := by linarith
    have hs : corrected 1 1 1 1 = 1 := by norm_num [corrected,gram]
    simp only [controlQep,qepTrace,fixed,controlNoise,teacher2,activation,mul_one,hs]
    rw [corrected_unit hd]
    congr 1 <;> field_simp <;> ring

theorem control_exact {epsilon : ℝ} (he : 0 < epsilon) :
    controlBaseU epsilon = 3*epsilon+epsilon^2 ∧
    controlQepU epsilon = 2*epsilon+epsilon^2 ∧
    controlBaseErr epsilon = 2*epsilon+epsilon^2 ∧
    controlQepErr epsilon = epsilon+epsilon^2 := by
  obtain ⟨hb,hq⟩ := control_closed he
  have hd : 1+epsilon ≠ 0 := by linarith
  have rb1 : residual1 fixed (controlBase epsilon) = -epsilon := by
    rw [hb]; dsimp [residual1,fixed]; ring
  have rq1 : residual1 fixed (controlQep epsilon) = -epsilon := by
    rw [hq]; dsimp [residual1,fixed]; ring
  have rb2 : residual2 fixed (controlBase epsilon) = -(2*epsilon+epsilon^2) := by
    rw [hb]; dsimp [residual2,fixed,teacher2,activation]; ring
  have rq2 : residual2 fixed (controlQep epsilon) = -(epsilon+epsilon^2) := by
    rw [hq]; dsimp [residual2,fixed,teacher2,activation]; field_simp; ring
  have h1 : 0 ≤ 2*epsilon+epsilon^2 := by positivity
  have h2 : 0 ≤ epsilon+epsilon^2 := by positivity
  refine ⟨?_,?_,?_,?_⟩
  · rw [controlBaseU,upper,rb1,rb2]
    simp only [abs_neg,abs_of_pos he,abs_of_nonneg h1]
    norm_num [fixed]
    ring
  · rw [controlQepU,upper,rq1,rq2]
    simp only [abs_neg,abs_of_pos he,abs_of_nonneg h2]
    norm_num [fixed]
    ring
  · rw [controlBaseErr,terminalError,hb]
    have hh : (1:ℝ)-(1+2*epsilon+epsilon^2) = -(2*epsilon+epsilon^2) := by ring
    simp only [teacherOutput,teacher2,activation,fixed,mul_one,hh,abs_neg]
    exact abs_of_nonneg h1
  · rw [controlQepErr,terminalError,hq]
    have hh : (1:ℝ)-(1+epsilon+epsilon^2) = -(epsilon+epsilon^2) := by ring
    simp only [teacherOutput,teacher2,activation,fixed,mul_one,hh,abs_neg]
    exact abs_of_nonneg h2

theorem control_reverse {epsilon : ℝ} (he : 0 < epsilon) :
    controlQepU epsilon-controlBaseU epsilon = -epsilon ∧
    controlQepU epsilon < controlBaseU epsilon ∧
    controlQepErr epsilon < controlBaseErr epsilon := by
  obtain ⟨hb,hq,heb,heq⟩ := control_exact he
  rw [hb,hq,heb,heq]
  constructor
  · ring
  constructor <;> linarith

end
end QepSharedE
