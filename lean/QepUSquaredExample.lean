import QepSharedE
import Mathlib.Data.Fintype.BigOperators










set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

namespace QepUSquared
noncomputable section
open QepSharedE (corrected gram activation)

structure Alphas where
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
structure Errs where
  e1 : ℝ
  e2 : ℝ
  e3 : ℝ



def qweight (alpha e z : ℝ) : ℝ := corrected alpha 1 1 z + e


def q1 (a : Alphas) (e : Errs) : ℝ := qweight a.a1 e.e1 1
def z2 (a : Alphas) (e : Errs) : ℝ := activation (q1 a e * 1)
def q2 (a : Alphas) (e : Errs) : ℝ := qweight a.a2 e.e2 (z2 a e)
def z3 (a : Alphas) (e : Errs) : ℝ := activation (q2 a e * z2 a e)
def q3 (a : Alphas) (e : Errs) : ℝ := qweight a.a3 e.e3 (z3 a e)
def z4 (a : Alphas) (e : Errs) : ℝ := activation (q3 a e * z3 a e)


def dev (z : ℝ) : ℝ := z - 1


def residual1 (a : Alphas) (e : Errs) : ℝ := 1*1 - q1 a e * 1
def residual2 (a : Alphas) (e : Errs) : ℝ := 1*1 - q2 a e * z2 a e
def residual3 (a : Alphas) (e : Errs) : ℝ := 1*1 - q3 a e * z3 a e

def upper (a : Alphas) (e : Errs) : ℝ := |residual1 a e| + |residual2 a e| + |residual3 a e|

def base : Alphas := ⟨0,0,0⟩
def qep : Alphas := ⟨0,1,0⟩
def sg : Bool → ℝ
  | true => 1
  | false => -1

def errs (t : ℝ) : Bool × Bool × Bool → Errs
  | (a, b, c) => ⟨sg a * t, sg b * 4, sg c * (4/3)⟩

def mean (f : Bool × Bool × Bool → ℝ) : ℝ := (1/8) * ∑ s, f s




theorem step_recursion {z : ℝ} (hz : z ≠ 0) (alpha e : ℝ) :
    dev (activation (qweight alpha e z * z)) = (1-alpha)*dev z + e*(1+dev z) := by
  unfold dev activation qweight corrected gram
  field_simp
  ring


theorem trace_recursion (a : Alphas) (e : Errs) (h2 : z2 a e ≠ 0) (h3 : z3 a e ≠ 0) :
    dev (z2 a e) = (1-a.a1)*dev 1 + e.e1*(1+dev 1) ∧
    dev (z3 a e) = (1-a.a2)*dev (z2 a e) + e.e2*(1+dev (z2 a e)) ∧
    dev (z4 a e) = (1-a.a3)*dev (z3 a e) + e.e3*(1+dev (z3 a e)) :=
  ⟨step_recursion one_ne_zero _ _, step_recursion h2 _ _, step_recursion h3 _ _⟩

theorem dev_one : dev 1 = 0 := by simp [dev]

theorem residual_eq (a : Alphas) (e : Errs) :
    residual1 a e = -dev (z2 a e) ∧ residual2 a e = -dev (z3 a e) ∧
    residual3 a e = -dev (z4 a e) := by
  simp only [residual1, residual2, residual3, z2, z3, z4, dev, activation]
  refine ⟨by ring, by ring, by ring⟩

theorem residual_z (a : Alphas) (e : Errs) :
    residual1 a e = 1 - z2 a e ∧ residual2 a e = 1 - z3 a e ∧ residual3 a e = 1 - z4 a e := by
  simp only [residual1, residual2, residual3, z2, z3, z4, activation]
  refine ⟨by ring, by ring, by ring⟩

theorem q_ne_zero (a : Alphas) (e : Errs) (h2 : z2 a e ≠ 0) (h3 : z3 a e ≠ 0)
    (h4 : z4 a e ≠ 0) : q1 a e ≠ 0 ∧ q2 a e ≠ 0 ∧ q3 a e ≠ 0 := by
  simp only [z2, z3, z4, activation] at h2 h3 h4
  exact ⟨left_ne_zero_of_mul h2, left_ne_zero_of_mul h3, left_ne_zero_of_mul h4⟩

theorem absP {x y : ℝ} (h : x = y) (hy : 0 ≤ y) : |x| = y := by rw [h, abs_of_nonneg hy]
theorem absN {x y : ℝ} (h : x = -y) (hy : 0 ≤ y) : |x| = y := by rw [h, abs_neg, abs_of_nonneg hy]



theorem z2_pos {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) (a : Bool) : 0 < 1 + sg a * t := by
  cases a <;> simp only [sg] <;> linarith


theorem base_closed (t : ℝ) (a b c : Bool) :
    z2 base (errs t (a,b,c)) = 1 + sg a * t ∧
    z3 base (errs t (a,b,c)) = (1 + sg b * 4) * (1 + sg a * t) ∧
    z4 base (errs t (a,b,c)) = (1 + sg c * (4/3)) * ((1 + sg b * 4) * (1 + sg a * t)) := by
  simp only [z2, z3, z4, q1, q2, q3, qweight, corrected, gram, activation, base, errs]
  refine ⟨by ring, by ring, by ring⟩


theorem qep_closed {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) (a b c : Bool) :
    z2 qep (errs t (a,b,c)) = 1 + sg a * t ∧
    z3 qep (errs t (a,b,c)) = 1 + sg b * 4 * (1 + sg a * t) ∧
    z4 qep (errs t (a,b,c)) = (1 + sg c * (4/3)) * (1 + sg b * 4 * (1 + sg a * t)) := by
  have hz : 1 + sg a * t ≠ 0 := ne_of_gt (z2_pos ht0 ht a)
  have h2 : z2 qep (errs t (a,b,c)) = 1 + sg a * t := by
    simp only [z2, q1, qweight, corrected, gram, activation, qep, errs]
    ring
  have h3 : z3 qep (errs t (a,b,c)) = 1 + sg b * 4 * (1 + sg a * t) := by
    rw [z3, q2, h2]
    simp only [qweight, corrected, gram, activation, qep, errs]
    field_simp
    ring
  have h4 : z4 qep (errs t (a,b,c)) = (1 + sg c * (4/3)) * (1 + sg b * 4 * (1 + sg a * t)) := by
    rw [z4, q3, h3]
    simp only [qweight, corrected, gram, activation, qep, errs]
    ring
  exact ⟨h2, h3, h4⟩



theorem base_z_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, true, true)) = 1 + 1*t ∧ z3 base (errs t (true, true, true)) = 5 + 5*t ∧
    z4 base (errs t (true, true, true)) = (35/3) + (35/3)*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t true true true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (true, true, true))) = 0 + 1*t ∧ dev (z3 base (errs t (true, true, true))) = 4 + 5*t ∧
    dev (z4 base (errs t (true, true, true))) = (32/3) + (35/3)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_ppp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, true, true)) ≠ 0 ∧ z3 base (errs t (true, true, true)) ≠ 0 ∧ z4 base (errs t (true, true, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_ppp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_gt (by linarith)⟩

theorem base_U_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (true, true, true)) = (44/3) + (53/3)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_ppp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (true, true, true))
  have r1 : |residual1 base (errs t (true, true, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 base (errs t (true, true, true))| = 4 + 5*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 base (errs t (true, true, true))| = (32/3) + (35/3)*t := by
    rw [e3, h4]; exact absN (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem base_z_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, true, false)) = 1 + 1*t ∧ z3 base (errs t (true, true, false)) = 5 + 5*t ∧
    z4 base (errs t (true, true, false)) = (-(5/3)) + (-(5/3))*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t true true false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (true, true, false))) = 0 + 1*t ∧ dev (z3 base (errs t (true, true, false))) = 4 + 5*t ∧
    dev (z4 base (errs t (true, true, false))) = (-(8/3)) + (-(5/3))*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_ppm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, true, false)) ≠ 0 ∧ z3 base (errs t (true, true, false)) ≠ 0 ∧ z4 base (errs t (true, true, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_ppm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_lt (by linarith)⟩

theorem base_U_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (true, true, false)) = (20/3) + (23/3)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_ppm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (true, true, false))
  have r1 : |residual1 base (errs t (true, true, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 base (errs t (true, true, false))| = 4 + 5*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 base (errs t (true, true, false))| = (8/3) + (5/3)*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem base_z_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, false, true)) = 1 + 1*t ∧ z3 base (errs t (true, false, true)) = (-3) + (-3)*t ∧
    z4 base (errs t (true, false, true)) = (-7) + (-7)*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t true false true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (true, false, true))) = 0 + 1*t ∧ dev (z3 base (errs t (true, false, true))) = (-4) + (-3)*t ∧
    dev (z4 base (errs t (true, false, true))) = (-8) + (-7)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_pmp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, false, true)) ≠ 0 ∧ z3 base (errs t (true, false, true)) ≠ 0 ∧ z4 base (errs t (true, false, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_pmp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_lt (by linarith)⟩

theorem base_U_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (true, false, true)) = 12 + 11*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_pmp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (true, false, true))
  have r1 : |residual1 base (errs t (true, false, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 base (errs t (true, false, true))| = 4 + 3*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 base (errs t (true, false, true))| = 8 + 7*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem base_z_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, false, false)) = 1 + 1*t ∧ z3 base (errs t (true, false, false)) = (-3) + (-3)*t ∧
    z4 base (errs t (true, false, false)) = 1 + 1*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t true false false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (true, false, false))) = 0 + 1*t ∧ dev (z3 base (errs t (true, false, false))) = (-4) + (-3)*t ∧
    dev (z4 base (errs t (true, false, false))) = 0 + 1*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_pmm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (true, false, false)) ≠ 0 ∧ z3 base (errs t (true, false, false)) ≠ 0 ∧ z4 base (errs t (true, false, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_pmm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_gt (by linarith)⟩

theorem base_U_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (true, false, false)) = 4 + 5*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_pmm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (true, false, false))
  have r1 : |residual1 base (errs t (true, false, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 base (errs t (true, false, false))| = 4 + 3*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 base (errs t (true, false, false))| = 0 + 1*t := by
    rw [e3, h4]; exact absN (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem base_z_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, true, true)) = 1 + (-1)*t ∧ z3 base (errs t (false, true, true)) = 5 + (-5)*t ∧
    z4 base (errs t (false, true, true)) = (35/3) + (-(35/3))*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t false true true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (false, true, true))) = 0 + (-1)*t ∧ dev (z3 base (errs t (false, true, true))) = 4 + (-5)*t ∧
    dev (z4 base (errs t (false, true, true))) = (32/3) + (-(35/3))*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mpp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, true, true)) ≠ 0 ∧ z3 base (errs t (false, true, true)) ≠ 0 ∧ z4 base (errs t (false, true, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_mpp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_gt (by linarith)⟩

theorem base_U_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (false, true, true)) = (44/3) + (-(47/3))*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mpp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (false, true, true))
  have r1 : |residual1 base (errs t (false, true, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 base (errs t (false, true, true))| = 4 + (-5)*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 base (errs t (false, true, true))| = (32/3) + (-(35/3))*t := by
    rw [e3, h4]; exact absN (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem base_z_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, true, false)) = 1 + (-1)*t ∧ z3 base (errs t (false, true, false)) = 5 + (-5)*t ∧
    z4 base (errs t (false, true, false)) = (-(5/3)) + (5/3)*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t false true false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (false, true, false))) = 0 + (-1)*t ∧ dev (z3 base (errs t (false, true, false))) = 4 + (-5)*t ∧
    dev (z4 base (errs t (false, true, false))) = (-(8/3)) + (5/3)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mpm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, true, false)) ≠ 0 ∧ z3 base (errs t (false, true, false)) ≠ 0 ∧ z4 base (errs t (false, true, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_mpm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_lt (by linarith)⟩

theorem base_U_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (false, true, false)) = (20/3) + (-(17/3))*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mpm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (false, true, false))
  have r1 : |residual1 base (errs t (false, true, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 base (errs t (false, true, false))| = 4 + (-5)*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 base (errs t (false, true, false))| = (8/3) + (-(5/3))*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem base_z_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, false, true)) = 1 + (-1)*t ∧ z3 base (errs t (false, false, true)) = (-3) + 3*t ∧
    z4 base (errs t (false, false, true)) = (-7) + 7*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t false false true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (false, false, true))) = 0 + (-1)*t ∧ dev (z3 base (errs t (false, false, true))) = (-4) + 3*t ∧
    dev (z4 base (errs t (false, false, true))) = (-8) + 7*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mmp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, false, true)) ≠ 0 ∧ z3 base (errs t (false, false, true)) ≠ 0 ∧ z4 base (errs t (false, false, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_mmp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_lt (by linarith)⟩

theorem base_U_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (false, false, true)) = 12 + (-9)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mmp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (false, false, true))
  have r1 : |residual1 base (errs t (false, false, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 base (errs t (false, false, true))| = 4 + (-3)*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 base (errs t (false, false, true))| = 8 + (-7)*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem base_z_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, false, false)) = 1 + (-1)*t ∧ z3 base (errs t (false, false, false)) = (-3) + 3*t ∧
    z4 base (errs t (false, false, false)) = 1 + (-1)*t := by
  obtain ⟨h2, h3, h4⟩ := base_closed t false false false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem base_dev_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 base (errs t (false, false, false))) = 0 + (-1)*t ∧ dev (z3 base (errs t (false, false, false))) = (-4) + 3*t ∧
    dev (z4 base (errs t (false, false, false))) = 0 + (-1)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mmm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem base_ne_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 base (errs t (false, false, false)) ≠ 0 ∧ z3 base (errs t (false, false, false)) ≠ 0 ∧ z4 base (errs t (false, false, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := base_z_mmm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_gt (by linarith)⟩

theorem base_U_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper base (errs t (false, false, false)) = 4 + (-1)*t := by
  obtain ⟨h2, h3, h4⟩ := base_z_mmm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z base (errs t (false, false, false))
  have r1 : |residual1 base (errs t (false, false, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 base (errs t (false, false, false))| = 4 + (-3)*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 base (errs t (false, false, false))| = 0 + 1*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring



theorem base_nonvanishing {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) (s : Bool × Bool × Bool) :
    z2 base (errs t s) ≠ 0 ∧ z3 base (errs t s) ≠ 0 ∧ z4 base (errs t s) ≠ 0 ∧
    q1 base (errs t s) ≠ 0 ∧ q2 base (errs t s) ≠ 0 ∧ q3 base (errs t s) ≠ 0 := by
  have hz : z2 base (errs t s) ≠ 0 ∧ z3 base (errs t s) ≠ 0 ∧ z4 base (errs t s) ≠ 0 := by
    obtain ⟨a, b, c⟩ := s
    cases a <;> cases b <;> cases c <;> first | exact base_ne_ppp ht0 ht | exact base_ne_ppm ht0 ht | exact base_ne_pmp ht0 ht | exact base_ne_pmm ht0 ht | exact base_ne_mpp ht0 ht | exact base_ne_mpm ht0 ht | exact base_ne_mmp ht0 ht | exact base_ne_mmm ht0 ht
  obtain ⟨h2, h3, h4⟩ := hz
  obtain ⟨g1, g2, g3⟩ := q_ne_zero base (errs t s) h2 h3 h4
  exact ⟨h2, h3, h4, g1, g2, g3⟩

theorem qep_z_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, true, true)) = 1 + 1*t ∧ z3 qep (errs t (true, true, true)) = 5 + 4*t ∧
    z4 qep (errs t (true, true, true)) = (35/3) + (28/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht true true true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (true, true, true))) = 0 + 1*t ∧ dev (z3 qep (errs t (true, true, true))) = 4 + 4*t ∧
    dev (z4 qep (errs t (true, true, true))) = (32/3) + (28/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_ppp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, true, true)) ≠ 0 ∧ z3 qep (errs t (true, true, true)) ≠ 0 ∧ z4 qep (errs t (true, true, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_ppp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_gt (by linarith)⟩

theorem qep_U_ppp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (true, true, true)) = (44/3) + (43/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_ppp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (true, true, true))
  have r1 : |residual1 qep (errs t (true, true, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (true, true, true))| = 4 + 4*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (true, true, true))| = (32/3) + (28/3)*t := by
    rw [e3, h4]; exact absN (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem qep_z_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, true, false)) = 1 + 1*t ∧ z3 qep (errs t (true, true, false)) = 5 + 4*t ∧
    z4 qep (errs t (true, true, false)) = (-(5/3)) + (-(4/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht true true false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (true, true, false))) = 0 + 1*t ∧ dev (z3 qep (errs t (true, true, false))) = 4 + 4*t ∧
    dev (z4 qep (errs t (true, true, false))) = (-(8/3)) + (-(4/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_ppm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, true, false)) ≠ 0 ∧ z3 qep (errs t (true, true, false)) ≠ 0 ∧ z4 qep (errs t (true, true, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_ppm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_lt (by linarith)⟩

theorem qep_U_ppm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (true, true, false)) = (20/3) + (19/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_ppm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (true, true, false))
  have r1 : |residual1 qep (errs t (true, true, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (true, true, false))| = 4 + 4*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (true, true, false))| = (8/3) + (4/3)*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem qep_z_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, false, true)) = 1 + 1*t ∧ z3 qep (errs t (true, false, true)) = (-3) + (-4)*t ∧
    z4 qep (errs t (true, false, true)) = (-7) + (-(28/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht true false true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (true, false, true))) = 0 + 1*t ∧ dev (z3 qep (errs t (true, false, true))) = (-4) + (-4)*t ∧
    dev (z4 qep (errs t (true, false, true))) = (-8) + (-(28/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_pmp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, false, true)) ≠ 0 ∧ z3 qep (errs t (true, false, true)) ≠ 0 ∧ z4 qep (errs t (true, false, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_pmp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_lt (by linarith)⟩

theorem qep_U_pmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (true, false, true)) = 12 + (43/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_pmp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (true, false, true))
  have r1 : |residual1 qep (errs t (true, false, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (true, false, true))| = 4 + 4*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (true, false, true))| = 8 + (28/3)*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem qep_z_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, false, false)) = 1 + 1*t ∧ z3 qep (errs t (true, false, false)) = (-3) + (-4)*t ∧
    z4 qep (errs t (true, false, false)) = 1 + (4/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht true false false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (true, false, false))) = 0 + 1*t ∧ dev (z3 qep (errs t (true, false, false))) = (-4) + (-4)*t ∧
    dev (z4 qep (errs t (true, false, false))) = 0 + (4/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_pmm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (true, false, false)) ≠ 0 ∧ z3 qep (errs t (true, false, false)) ≠ 0 ∧ z4 qep (errs t (true, false, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_pmm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_gt (by linarith)⟩

theorem qep_U_pmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (true, false, false)) = 4 + (19/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_pmm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (true, false, false))
  have r1 : |residual1 qep (errs t (true, false, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absN (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (true, false, false))| = 4 + 4*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (true, false, false))| = 0 + (4/3)*t := by
    rw [e3, h4]; exact absN (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem qep_z_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, true, true)) = 1 + (-1)*t ∧ z3 qep (errs t (false, true, true)) = 5 + (-4)*t ∧
    z4 qep (errs t (false, true, true)) = (35/3) + (-(28/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht false true true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (false, true, true))) = 0 + (-1)*t ∧ dev (z3 qep (errs t (false, true, true))) = 4 + (-4)*t ∧
    dev (z4 qep (errs t (false, true, true))) = (32/3) + (-(28/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mpp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, true, true)) ≠ 0 ∧ z3 qep (errs t (false, true, true)) ≠ 0 ∧ z4 qep (errs t (false, true, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mpp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_gt (by linarith)⟩

theorem qep_U_mpp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (false, true, true)) = (44/3) + (-(37/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mpp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (false, true, true))
  have r1 : |residual1 qep (errs t (false, true, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (false, true, true))| = 4 + (-4)*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (false, true, true))| = (32/3) + (-(28/3))*t := by
    rw [e3, h4]; exact absN (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem qep_z_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, true, false)) = 1 + (-1)*t ∧ z3 qep (errs t (false, true, false)) = 5 + (-4)*t ∧
    z4 qep (errs t (false, true, false)) = (-(5/3)) + (4/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht false true false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (false, true, false))) = 0 + (-1)*t ∧ dev (z3 qep (errs t (false, true, false))) = 4 + (-4)*t ∧
    dev (z4 qep (errs t (false, true, false))) = (-(8/3)) + (4/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mpm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, true, false)) ≠ 0 ∧ z3 qep (errs t (false, true, false)) ≠ 0 ∧ z4 qep (errs t (false, true, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mpm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_lt (by linarith)⟩

theorem qep_U_mpm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (false, true, false)) = (20/3) + (-(13/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mpm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (false, true, false))
  have r1 : |residual1 qep (errs t (false, true, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (false, true, false))| = 4 + (-4)*t := by
    rw [e2, h3]; exact absN (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (false, true, false))| = (8/3) + (-(4/3))*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem qep_z_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, false, true)) = 1 + (-1)*t ∧ z3 qep (errs t (false, false, true)) = (-3) + 4*t ∧
    z4 qep (errs t (false, false, true)) = (-7) + (28/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht false false true
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (false, false, true))) = 0 + (-1)*t ∧ dev (z3 qep (errs t (false, false, true))) = (-4) + 4*t ∧
    dev (z4 qep (errs t (false, false, true))) = (-8) + (28/3)*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mmp ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, false, true)) ≠ 0 ∧ z3 qep (errs t (false, false, true)) ≠ 0 ∧ z4 qep (errs t (false, false, true)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mmp ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_lt (by linarith)⟩

theorem qep_U_mmp {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (false, false, true)) = 12 + (-(37/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mmp ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (false, false, true))
  have r1 : |residual1 qep (errs t (false, false, true))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (false, false, true))| = 4 + (-4)*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (false, false, true))| = 8 + (-(28/3))*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring

theorem qep_z_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, false, false)) = 1 + (-1)*t ∧ z3 qep (errs t (false, false, false)) = (-3) + 4*t ∧
    z4 qep (errs t (false, false, false)) = 1 + (-(4/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_closed ht0 ht false false false
  refine ⟨h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;> simp only [sg] <;> ring

theorem qep_dev_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    dev (z2 qep (errs t (false, false, false))) = 0 + (-1)*t ∧ dev (z3 qep (errs t (false, false, false))) = (-4) + 4*t ∧
    dev (z4 qep (errs t (false, false, false))) = 0 + (-(4/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mmm ht0 ht
  rw [h2, h3, h4]
  simp only [dev]
  refine ⟨by ring, by ring, by ring⟩

theorem qep_ne_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    z2 qep (errs t (false, false, false)) ≠ 0 ∧ z3 qep (errs t (false, false, false)) ≠ 0 ∧ z4 qep (errs t (false, false, false)) ≠ 0 := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mmm ht0 ht
  rw [h2, h3, h4]
  refine ⟨ne_of_gt (by linarith), ne_of_lt (by linarith), ne_of_gt (by linarith)⟩

theorem qep_U_mmm {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    upper qep (errs t (false, false, false)) = 4 + (-(5/3))*t := by
  obtain ⟨h2, h3, h4⟩ := qep_z_mmm ht0 ht
  obtain ⟨e1, e2, e3⟩ := residual_z qep (errs t (false, false, false))
  have r1 : |residual1 qep (errs t (false, false, false))| = 0 + 1*t := by
    rw [e1, h2]; exact absP (by ring) (by linarith)
  have r2 : |residual2 qep (errs t (false, false, false))| = 4 + (-4)*t := by
    rw [e2, h3]; exact absP (by ring) (by linarith)
  have r3 : |residual3 qep (errs t (false, false, false))| = 0 + (4/3)*t := by
    rw [e3, h4]; exact absP (by ring) (by linarith)
  rw [upper, r1, r2, r3]
  ring



theorem qep_nonvanishing {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) (s : Bool × Bool × Bool) :
    z2 qep (errs t s) ≠ 0 ∧ z3 qep (errs t s) ≠ 0 ∧ z4 qep (errs t s) ≠ 0 ∧
    q1 qep (errs t s) ≠ 0 ∧ q2 qep (errs t s) ≠ 0 ∧ q3 qep (errs t s) ≠ 0 := by
  have hz : z2 qep (errs t s) ≠ 0 ∧ z3 qep (errs t s) ≠ 0 ∧ z4 qep (errs t s) ≠ 0 := by
    obtain ⟨a, b, c⟩ := s
    cases a <;> cases b <;> cases c <;> first | exact qep_ne_ppp ht0 ht | exact qep_ne_ppm ht0 ht | exact qep_ne_pmp ht0 ht | exact qep_ne_pmm ht0 ht | exact qep_ne_mpp ht0 ht | exact qep_ne_mpm ht0 ht | exact qep_ne_mmp ht0 ht | exact qep_ne_mmm ht0 ht
  obtain ⟨h2, h3, h4⟩ := hz
  obtain ⟨g1, g2, g3⟩ := q_ne_zero qep (errs t s) h2 h3 h4
  exact ⟨h2, h3, h4, g1, g2, g3⟩



theorem mean_base_sq {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    mean (fun s => (upper base (errs t s))^2) = 2*(493*t^2 + 93*t + 472)/9 := by
  simp only [mean, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [base_U_ppp ht0 ht, base_U_ppm ht0 ht, base_U_pmp ht0 ht, base_U_pmm ht0 ht, base_U_mpp ht0 ht, base_U_mpm ht0 ht, base_U_mmp ht0 ht, base_U_mmm ht0 ht]
  ring

theorem mean_qep_sq {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    mean (fun s => (upper qep (errs t s))^2) = (919*t^2 + 192*t + 944)/9 := by
  simp only [mean, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [qep_U_ppp ht0 ht, qep_U_ppm ht0 ht, qep_U_pmp ht0 ht, qep_U_pmm ht0 ht, qep_U_mpp ht0 ht, qep_U_mpm ht0 ht, qep_U_mmp ht0 ht, qep_U_mmm ht0 ht]
  ring


theorem mean_sq_gap {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) :
    mean (fun s => (upper qep (errs t s))^2) - mean (fun s => (upper base (errs t s))^2)
      = t*(6 - 67*t)/9 ∧
    0 < t*(6 - 67*t)/9 ∧
    mean (fun s => (upper base (errs t s))^2) < mean (fun s => (upper qep (errs t s))^2) := by
  have hpos : 0 < t*(6 - 67*t) := mul_pos ht0 (by linarith)
  have hg : mean (fun s => (upper qep (errs t s))^2) - mean (fun s => (upper base (errs t s))^2)
      = t*(6 - 67*t)/9 := by
    rw [mean_base_sq ht0 ht, mean_qep_sq ht0 ht]; ring
  have hp : 0 < t*(6 - 67*t)/9 := by positivity
  exact ⟨hg, hp, by linarith⟩



theorem recursion_holds {t : ℝ} (ht0 : 0 < t) (ht : t < 6/67) (s : Bool × Bool × Bool) :
    (dev (z3 base (errs t s)) = (1-0)*dev (z2 base (errs t s)) + (errs t s).e2*(1+dev (z2 base (errs t s)))) ∧
    (dev (z3 qep (errs t s)) = (1-1)*dev (z2 qep (errs t s)) + (errs t s).e2*(1+dev (z2 qep (errs t s)))) := by
  obtain ⟨b2, b3, -⟩ := base_nonvanishing ht0 ht s
  obtain ⟨c2, c3, -⟩ := qep_nonvanishing ht0 ht s
  exact ⟨(trace_recursion base (errs t s) b2 b3).2.1, (trace_recursion qep (errs t s) c2 c3).2.1⟩

end
end QepUSquared
