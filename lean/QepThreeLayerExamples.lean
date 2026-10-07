import QepSharedE
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace QepThreeLayerExamples
noncomputable section




structure Trace where
  q1 : ℝ
  q2 : ℝ
  q3 : ℝ
  z2 : ℝ
  z3 : ℝ
  z4 : ℝ

def base (e1 e2 e3 : ℝ) : Trace :=
  let q1 := 1 + e1
  let q2 := 1 + e2
  let q3 := 1 + e3
  let z2 := q1 * 1
  let z3 := q2 * z2
  ⟨q1,q2,q3,z2,z3,q3*z3⟩

def qep (e1 e2 e3 : ℝ) : Trace :=
  let q1 := QepSharedE.corrected 1 1 1 1 + e1
  let z2 := q1 * 1
  let q2 := QepSharedE.corrected 1 1 1 z2 + e2
  let z3 := q2 * z2
  let q3 := QepSharedE.corrected 1 1 1 z3 + e3
  ⟨q1,q2,q3,z2,z3,q3*z3⟩

def residual1 (s : Trace) : ℝ := 1 - s.q1 * 1
def residual2 (s : Trace) : ℝ := 1 - s.q2 * s.z2
def residual3 (s : Trace) : ℝ := 1 - s.q3 * s.z3
def common2 (e2 : ℝ) (s : Trace) : ℝ := 1 - (1+e2)*s.z2
def common3 (e3 : ℝ) (s : Trace) : ℝ := 1 - (1+e3)*s.z3
def upper (s : Trace) : ℝ := |residual1 s| + |residual2 s| + |residual3 s|
def terminalError (s : Trace) : ℝ := |1-s.z4|
def Positive (s : Trace) : Prop :=
  0 < s.q1 ∧ 0 < s.q2 ∧ 0 < s.q3 ∧ 0 < s.z2 ∧ 0 < s.z3

theorem actual_corrected_step (e y : ℝ) (hy : y ≠ 0) :
    (QepSharedE.corrected 1 1 1 y + e)*y = 1+e*y := by
  rw [QepSharedE.corrected_unit hy]
  field_simp

theorem qep_closed (e1 e2 e3 : ℝ) (h2 : 1+e1 ≠ 0)
    (h3 : 1+e2*(1+e1) ≠ 0) :
    qep e1 e2 e3 = ⟨1+e1,1/(1+e1)+e2,1/(1+e2*(1+e1))+e3,
      1+e1,1+e2*(1+e1),1+e3*(1+e2*(1+e1))⟩ := by
  have h1 : QepSharedE.corrected 1 1 1 1 = 1 := by
    norm_num [QepSharedE.corrected,QepSharedE.gram]
  have hstep2 := actual_corrected_step e2 (1+e1) h2
  have hstep3 := actual_corrected_step e3 (1+e2*(1+e1)) h3
  simp only [qep,h1,mul_one,hstep2,hstep3]
  rw [QepSharedE.corrected_unit h2,QepSharedE.corrected_unit h3]

theorem qep_residuals (e1 e2 e3 : ℝ) (h2 : 1+e1 ≠ 0)
    (h3 : 1+e2*(1+e1) ≠ 0) :
    residual1 (qep e1 e2 e3) = -e1 ∧
    residual2 (qep e1 e2 e3) = -e2*(1+e1) ∧
    residual3 (qep e1 e2 e3) = -e3*(1+e2*(1+e1)) := by
  rw [qep_closed e1 e2 e3 h2 h3]
  dsimp [residual1,residual2,residual3]
  constructor
  · ring
  constructor <;> field_simp <;> ring

theorem positive_qep (e1 e2 e3 : ℝ) (h2 : 0 < 1+e1)
    (h3 : 0 < 1+e2*(1+e1)) (h4 : 0 < 1+e3*(1+e2*(1+e1))) :
    Positive (qep e1 e2 e3) := by
  rw [qep_closed e1 e2 e3 (ne_of_gt h2) (ne_of_gt h3)]
  have p2 : 0 < 1/(1+e1)+e2 := by
    have h : (1/(1+e1)+e2)*(1+e1) = 1+e2*(1+e1) := by
      field_simp
    exact (mul_pos_iff_of_pos_right h2).mp (h ▸ h3)
  have p3 : 0 < 1/(1+e2*(1+e1))+e3 := by
    have h : (1/(1+e2*(1+e1))+e3)*(1+e2*(1+e1)) =
        1+e3*(1+e2*(1+e1)) := by field_simp
    exact (mul_pos_iff_of_pos_right h3).mp (h ▸ h4)
  exact ⟨h2,p2,p3,h2,h3⟩

theorem positive_grams (s : Trace) (h : Positive s) :
    0 < QepSharedE.gram 1 ∧ 0 < QepSharedE.gram s.z2 ∧
    0 < QepSharedE.gram s.z3 := by
  obtain ⟨_,_,_,h2,h3⟩ := h
  simp only [QepSharedE.gram]
  exact ⟨by norm_num,sq_pos_of_pos h2,sq_pos_of_pos h3⟩

def trajectoryBase (t : ℝ) := base (t/2) (-t/10) (-7*t/27)
def trajectoryQep (t : ℝ) := qep (t/2) (-t/10) (-7*t/27)
def compositeBase (t : ℝ) := base (-t/2) (-t/2) (3*t)
def compositeQep (t : ℝ) := qep (-t/2) (-t/2) (3*t)

theorem trajectory_input_bounds {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    0 < 1+t/2 ∧ 0 < 1+(-t/10)*(1+t/2) ∧
    1+(-t/10)*(1+t/2) ≤ 1 ∧
    0 < 1+(-7*t/27)*(1+(-t/10)*(1+t/2)) := by
  have ht2 : t^2 ≤ t := by nlinarith [mul_nonneg (le_of_lt ht) (sub_nonneg.mpr hu)]
  have h3 : 0 < 1+(-t/10)*(1+t/2) := by nlinarith
  have h3u : 1+(-t/10)*(1+t/2) ≤ 1 := by nlinarith [sq_nonneg t]
  have hp : t*(1+(-t/10)*(1+t/2)) ≤ 1 :=
    (mul_le_mul hu h3u (le_of_lt h3) (by norm_num)).trans_eq (by ring)
  exact ⟨by linarith,h3,h3u,by nlinarith⟩

theorem trajectory_legal {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    Positive (trajectoryBase t) ∧ Positive (trajectoryQep t) := by
  obtain ⟨h2,h3,_,h4⟩ := trajectory_input_bounds ht hu
  constructor
  · dsimp [Positive,trajectoryBase,base]
    have p2 : 0 < 1 + -t/10 := by linarith
    have p3 : 0 < 1 + -7*t/27 := by linarith
    exact ⟨h2,p2,p3,by linarith,mul_pos p2 (by linarith)⟩
  · exact positive_qep _ _ _ h2 h3 h4

theorem trajectory_residuals {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    residual1 (trajectoryQep t) = -t/2 ∧
    residual2 (trajectoryQep t) = t*(2+t)/20 ∧
    residual3 (trajectoryQep t) = t*(140-14*t-7*t^2)/540 ∧
    residual3 (trajectoryBase t) = -t*(1-t)*(76-7*t)/540 ∧
    common2 (-t/10) (trajectoryQep t) = -t*(8-t)/20 ∧
    common3 (-7*t/27) (trajectoryQep t) =
      t*(140-14*t-7*t^2)/540 + t/10+t^2/20 := by
  obtain ⟨h2,h3,_,_⟩ := trajectory_input_bounds ht hu
  obtain ⟨r1,r2,r3⟩ := qep_residuals (t/2) (-t/10) (-7*t/27) (ne_of_gt h2) (ne_of_gt h3)
  change residual1 (qep _ _ _) = _ ∧ residual2 (qep _ _ _) = _ ∧
    residual3 (qep _ _ _) = _ ∧ _
  rw [r1,r2,r3]
  refine ⟨by ring,by ring,by ring,?_,?_,?_⟩
  · dsimp [residual3,trajectoryBase,base]; ring
  · rw [trajectoryQep,qep_closed _ _ _ (ne_of_gt h2) (ne_of_gt h3)]
    dsimp [common2]; ring
  · rw [trajectoryQep,qep_closed _ _ _ (ne_of_gt h2) (ne_of_gt h3)]
    dsimp [common3]; ring

theorem trajectory_common_input_comparison {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    |residual1 (trajectoryQep t)| = |residual1 (trajectoryBase t)| ∧
    |residual2 (trajectoryQep t)| ≤ |common2 (-t/10) (trajectoryQep t)| ∧
    |residual3 (trajectoryQep t)| ≤ |common3 (-7*t/27) (trajectoryQep t)| := by
  obtain ⟨r1,r2,r3,_,c2,c3⟩ := trajectory_residuals ht hu
  have hq2 : 0 ≤ t*(2+t)/20 := by positivity
  have hc2 : -t*(8-t)/20 ≤ 0 := by
    have : 0 ≤ t*(8-t) := mul_nonneg (le_of_lt ht) (by linarith)
    nlinarith
  have ht2 : t^2 ≤ t := by nlinarith [mul_nonneg (le_of_lt ht) (sub_nonneg.mpr hu)]
  have hq3 : 0 ≤ t*(140-14*t-7*t^2)/540 := by
    have : 0 ≤ 140-14*t-7*t^2 := by nlinarith
    positivity
  have hc3 : 0 ≤ t*(140-14*t-7*t^2)/540+t/10+t^2/20 := by positivity
  rw [r1,r2,r3,c2,c3,abs_of_nonneg hq2,abs_of_nonpos hc2,
    abs_of_nonneg hq3,abs_of_nonneg hc3]
  refine ⟨?_,?_,?_⟩
  · congr 1; dsimp [residual1,trajectoryBase,base]; ring
  · have : 0 ≤ t*(3-t) := mul_nonneg (le_of_lt ht) (by linarith)
    nlinarith
  · nlinarith [sq_nonneg t]

theorem trajectory_actual_gap {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    |residual3 (trajectoryQep t)| - |residual3 (trajectoryBase t)| =
      t*(64+69*t-14*t^2)/540 ∧
    |residual3 (trajectoryBase t)| < |residual3 (trajectoryQep t)| := by
  obtain ⟨_,_,rq,rb,_,_⟩ := trajectory_residuals ht hu
  have ht2 : t^2 ≤ t := by nlinarith [mul_nonneg (le_of_lt ht) (sub_nonneg.mpr hu)]
  have hq : 0 ≤ t*(140-14*t-7*t^2)/540 := by
    have : 0 ≤ 140-14*t-7*t^2 := by nlinarith
    positivity
  have hb : -t*(1-t)*(76-7*t)/540 ≤ 0 := by
    have : 0 ≤ t*(1-t)*(76-7*t) := by
      exact mul_nonneg (mul_nonneg (le_of_lt ht) (by linarith)) (by linarith)
    nlinarith
  have hg : 0 < t*(64+69*t-14*t^2)/540 := by
    have : 0 < 64+69*t-14*t^2 := by nlinarith
    positivity
  rw [rq,rb,abs_of_nonneg hq,abs_of_nonpos hb]
  constructor
  · ring
  · nlinarith [hg]

theorem trajectory_first_order {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    |(|residual3 (trajectoryQep t)| - |residual3 (trajectoryBase t)|) -
      (16/135:ℝ)*t| ≤ (23/180:ℝ)*t^2 := by
  rw [(trajectory_actual_gap ht hu).1]
  have h : t*(64+69*t-14*t^2)/540-(16/135:ℝ)*t = t^2*(69-14*t)/540 := by ring
  have hcoef : 0 ≤ 69-14*t := by linarith
  rw [h,abs_of_nonneg (by positivity : 0 ≤ t^2*(69-14*t)/540)]
  have : 0 ≤ t^2*(14*t) := by positivity
  nlinarith

theorem trajectory_numeric :
    trajectoryBase 1 = ⟨3/2,9/10,20/27,3/2,27/20,1⟩ ∧
    trajectoryQep 1 = ⟨3/2,17/30,421/459,3/2,17/20,421/540⟩ ∧
    residual3 (trajectoryBase 1) = 0 ∧ residual3 (trajectoryQep 1) = 119/540 := by
  norm_num [trajectoryBase,trajectoryQep,base,qep,QepSharedE.corrected,
    QepSharedE.gram,residual3]

theorem composite_input_bounds {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    0 < 1 + -t/2 ∧ 0 < 1+(-t/2)*(1 + -t/2) ∧
    0 < 1+(3*t)*(1+(-t/2)*(1 + -t/2)) := by
  have h2 : 0 < 1 + -t/2 := by linarith
  have h3 : 0 < 1+(-t/2)*(1 + -t/2) := by nlinarith [sq_nonneg t]
  exact ⟨h2,h3,by positivity⟩

theorem composite_legal {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    Positive (compositeBase t) ∧ Positive (compositeQep t) := by
  obtain ⟨h2,h3,h4⟩ := composite_input_bounds ht hu
  constructor
  · dsimp [Positive,compositeBase,base]
    exact ⟨h2,h2,by linarith,by linarith,mul_pos h2 (by linarith)⟩
  · exact positive_qep _ _ _ h2 h3 h4

theorem composite_residuals {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    residual1 (compositeBase t) = t/2 ∧
    residual2 (compositeBase t) = t*(1-t/4) ∧
    residual3 (compositeBase t) = -t*(1-t)*(8-3*t)/4 ∧
    residual3 (compositeQep t) = -3*t*(1-t/2+t^2/4) := by
  obtain ⟨h2,h3,_⟩ := composite_input_bounds ht hu
  obtain ⟨_,_,rq⟩ := qep_residuals (-t/2) (-t/2) (3*t) (ne_of_gt h2) (ne_of_gt h3)
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [residual1,compositeBase,base]; ring
  · dsimp [residual2,compositeBase,base]; ring
  · dsimp [residual3,compositeBase,base]; ring
  · change residual3 (qep _ _ _) = _
    rw [rq]; ring

theorem actual_terminal_residual (e1 e2 e3 : ℝ) :
    terminalError (base e1 e2 e3) = |residual3 (base e1 e2 e3)| ∧
    terminalError (qep e1 e2 e3) = |residual3 (qep e1 e2 e3)| := by
  exact ⟨rfl,rfl⟩

theorem composite_exact_errors {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    upper (compositeBase t) = (7/2:ℝ)*t-3*t^2+(3/4:ℝ)*t^3 ∧
    terminalError (compositeQep t) = 3*t-(3/2:ℝ)*t^2+(3/4:ℝ)*t^3 := by
  obtain ⟨r1,r2,r3,rq⟩ := composite_residuals ht hu
  have h1 : 0 ≤ t/2 := by positivity
  have h2 : 0 ≤ t*(1-t/4) := mul_nonneg (le_of_lt ht) (by linarith)
  have h3 : -t*(1-t)*(8-3*t)/4 ≤ 0 := by
    have : 0 ≤ t*(1-t)*(8-3*t) :=
      mul_nonneg (mul_nonneg (le_of_lt ht) (by linarith)) (by linarith)
    nlinarith
  have hq : -3*t*(1-t/2+t^2/4) ≤ 0 := by
    have : 0 ≤ 1-t/2+t^2/4 := by nlinarith [sq_nonneg t]
    have hp : 0 ≤ 3*t*(1-t/2+t^2/4) := by positivity
    nlinarith
  constructor
  · rw [upper,r1,r2,r3,abs_of_nonneg h1,abs_of_nonneg h2,abs_of_nonpos h3]
    ring
  · change terminalError (qep _ _ _) = _
    rw [(actual_terminal_residual _ _ _).2]
    change |residual3 (compositeQep t)| = _
    rw [rq,abs_of_nonpos hq]; ring

theorem composite_actual_gap {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    terminalError (compositeQep t) - upper (compositeBase t) = t*(3*t-1)/2 := by
  obtain ⟨hb,hq⟩ := composite_exact_errors ht hu
  rw [hb,hq]; ring

theorem composite_violation_iff {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    upper (compositeBase t) < terminalError (compositeQep t) ↔ (1/3:ℝ) < t := by
  have hg := composite_actual_gap ht hu
  constructor
  · intro h
    by_contra hn
    have hfactor : 3*t-1 ≤ 0 := by linarith
    have : t*(3*t-1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) hfactor
    nlinarith
  · intro h
    have hfactor : 0 < 3*t-1 := by linarith
    have : 0 < t*(3*t-1) := mul_pos ht hfactor
    linarith

theorem composite_first_order {t : ℝ} (ht : 0 < t) (hu : t ≤ 1) :
    |terminalError (compositeQep t)-3*t| ≤ (3/2:ℝ)*t^2 ∧
    |upper (compositeBase t)-(7/2:ℝ)*t| ≤ 3*t^2 ∧
    (terminalError (compositeQep t)-upper (compositeBase t))/t = (3*t-1)/2 := by
  obtain ⟨hb,hq⟩ := composite_exact_errors ht hu
  have h3 : 0 ≤ t^3 := by positivity
  have h3u : t^3 ≤ t^2 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hu)]
  rw [hb,hq]
  have p1 : 3*t-(3/2:ℝ)*t^2+(3/4:ℝ)*t^3-3*t ≤ 0 := by nlinarith
  have p2 : (7/2:ℝ)*t-3*t^2+(3/4:ℝ)*t^3-(7/2:ℝ)*t ≤ 0 := by nlinarith
  rw [abs_of_nonpos p1,abs_of_nonpos p2]
  refine ⟨by nlinarith,by nlinarith,?_⟩
  field_simp; ring

theorem composite_numeric :
    compositeBase 1 = ⟨1/2,1/2,4,1/2,1/4,1⟩ ∧
    compositeQep 1 = ⟨1/2,3/2,13/3,1/2,3/4,13/4⟩ ∧
    residual1 (compositeBase 1) = 1/2 ∧
    residual2 (compositeBase 1) = 3/4 ∧
    residual3 (compositeBase 1) = 0 ∧
    upper (compositeBase 1) = 5/4 ∧
    terminalError (compositeQep 1) = 9/4 := by
  norm_num [compositeBase,compositeQep,base,qep,QepSharedE.corrected,
    QepSharedE.gram,residual1,residual2,residual3,upper,terminalError]



theorem composite_outside_domain :
    terminalError (compositeQep (3/2)) - upper (compositeBase (3/2)) = 21/16 ∧
    terminalError (compositeQep (3/2)) - upper (compositeBase (3/2)) ≠
      (3/2:ℝ)*(3*(3/2)-1)/2 := by
  norm_num [compositeBase,compositeQep,base,qep,QepSharedE.corrected,
    QepSharedE.gram,residual1,residual2,residual3,upper,terminalError]

theorem shared_errors_recovered (e1 e2 e3 : ℝ) :
    (base e1 e2 e3).q1-1=e1 ∧ (base e1 e2 e3).q2-1=e2 ∧
    (base e1 e2 e3).q3-1=e3 ∧
    (qep e1 e2 e3).q1-QepSharedE.corrected 1 1 1 1=e1 ∧
    (qep e1 e2 e3).q2-QepSharedE.corrected 1 1 1 (qep e1 e2 e3).z2=e2 ∧
    (qep e1 e2 e3).q3-QepSharedE.corrected 1 1 1 (qep e1 e2 e3).z3=e3 := by
  simp [base,qep]

end
end QepThreeLayerExamples
