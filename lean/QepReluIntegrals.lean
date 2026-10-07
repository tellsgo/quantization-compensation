import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
set_option maxHeartbeats 500000
open MeasureTheory Set
namespace QepReluIntegrals
noncomputable section

def relu (x : ℝ) : ℝ := max 0 x

theorem integral_relu_square (a b c z : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (hz : 0 ≤ z) :
    (∫ v in a..b, (relu (z*(v-c)))^2) = z^2*(b-c)^3/3 := by
  have hc : Continuous (fun v : ℝ => (relu (z*(v-c)))^2) := by unfold relu; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a c) (hc.intervalIntegrable c b)]
  have hzero : (∫ v in a..c, (relu (z*(v-c)))^2)=0 := by
    calc
      _ = ∫ v in a..c, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hac] at hv
        simp [relu, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hz (sub_nonpos.mpr hv.2))]
      _ = 0 := by simp
  rw [hzero, zero_add]
  have heq : (∫ v in c..b, (relu (z*(v-c)))^2) = ∫ v in c..b, z^2*(v-c)^2 := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hcb] at hv
    change (max 0 (z*(v-c)))^2 = z^2*(v-c)^2
    rw [max_eq_right (mul_nonneg hz (sub_nonneg.mpr hv.1)), mul_pow]
  rw [heq, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_right (fun v : ℝ => v^2) c]
  rw [integral_pow]
  ring

theorem base_inner : (∫ v in (-(1/2:ℝ))..(1/2), (relu (v-1/4))^2)=1/192 := by
  have h := integral_relu_square (-(1/2:ℝ)) (1/2) (1/4) 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num only [one_mul] at h
  convert h using 1

theorem qep_inner (z : ℝ) (hz : 1/2 ≤ z) :
    (∫ v in (-(1/2:ℝ))..(1/2), (relu (v*z-1/4))^2)=
      z^2/24-z/16+1/32-1/(192*z) := by
  have hpos : 0 < z := by linarith
  have hcut : 1/(4*z) ≤ (1/2:ℝ) := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hlo : -(1/2:ℝ) ≤ 1/(4*z) := le_trans (show -(1/2:ℝ) ≤ 0 by norm_num) (by positivity)
  have heq : (fun v : ℝ => relu (v*z-1/4)^2) = fun v => relu (z*(v-1/(4*z)))^2 := by
    funext v
    congr 2
    field_simp [ne_of_gt hpos]
  rw [heq, integral_relu_square _ _ _ _ hlo hcut hpos.le]
  field_simp [ne_of_gt hpos]
  ring

theorem log_three_lt : Real.log 3 < (4/3:ℝ) := by
  have hc : ContinuousOn (fun x : ℝ => 1/x) (Icc (1/2) (3/2)) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx; change x ≠ 0; linarith [hx.1]
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (1/2:ℝ)<3/2) hc
    (show ContinuousOn (fun x : ℝ => (8-4*x)/3) (Icc (1/2) (3/2)) from (by fun_prop))
    (by
      intro x hx
      have hxpos : 0<x := by linarith [hx.1]
      apply (div_le_iff₀ hxpos).2
      have hp := mul_nonneg (show 0≤x-1/2 by linarith [hx.1]) (show 0≤3/2-x by linarith [hx.2])
      nlinarith)
    (by refine ⟨1, by norm_num, by norm_num⟩)
  rw [integral_one_div_of_pos (by norm_num) (by norm_num)] at h
  norm_num only [show (3/2:ℝ)/(1/2)=3 by norm_num] at h
  have hi : (∫ x in (1/2:ℝ)..(3/2), (8-4*x)/3)=(4/3:ℝ) := by
    have h4 : IntervalIntegrable (fun x : ℝ => 4*x) volume (1/2) (3/2) := (by fun_prop : Continuous (fun x : ℝ => 4*x)).intervalIntegrable _ _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable _ _) h4,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    norm_num
  rwa [hi] at h


theorem base_outer : (∫ z in (1/2:ℝ)..(3/2), z^2/192)=13/2304 := by
  rw [intervalIntegral.integral_div, integral_pow]
  norm_num

theorem qep_outer :
    (∫ z in (1/2:ℝ)..(3/2), z^2/24-z/16+1/32-1/(192*z))=
      1/72-Real.log 3/192 := by
  have hp : Continuous (fun z : ℝ => z^2/24-z/16+1/32) := by fun_prop
  have hp2 : Continuous (fun z : ℝ => z^2/24) := by fun_prop
  have hp1 : Continuous (fun z : ℝ => z/16) := by fun_prop
  have hi : IntervalIntegrable (fun z : ℝ => 1/z) volume (1/2) (3/2) := by
    have hc : ContinuousOn (fun z : ℝ => 1/z) (Icc (1/2) (3/2)) := by
      apply continuousOn_const.div continuousOn_id
      intro z hz; change z ≠ 0; linarith [hz.1]
    exact hc.intervalIntegrable_of_Icc (by norm_num)
  have heq (z : ℝ) : 1/(192*z) = (1/z)/192 := by ring
  simp_rw [heq]
  rw [intervalIntegral.integral_sub (hp.intervalIntegrable _ _) (hi.div_const 192),
    intervalIntegral.integral_add (f:=fun z : ℝ => z^2/24-z/16) (g:=fun _ : ℝ => 1/32) ((hp2.sub hp1).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hp2.intervalIntegrable _ _) (hp1.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_div (24:ℝ) (fun z : ℝ => z^2),
    intervalIntegral.integral_div (16:ℝ) (fun z : ℝ => z),
    intervalIntegral.integral_div (192:ℝ) (fun z : ℝ => 1/z),
    integral_pow, integral_id, intervalIntegral.integral_const,
    integral_one_div_of_pos (by norm_num) (by norm_num)]
  norm_num

theorem log_three_gt : (1:ℝ) < Real.log 3 := by
  have hc : ContinuousOn (fun x : ℝ => 1/x) (Icc (1/2) (3/2)) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx; change x ≠ 0; linarith [hx.1]
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (1/2:ℝ)<3/2)
    (show ContinuousOn (fun x : ℝ => 2-x) (Icc (1/2) (3/2)) from (by fun_prop)) hc
    (by
      intro x hx
      have hxpos : 0<x := by linarith [hx.1]
      apply (le_div_iff₀ hxpos).2
      nlinarith [sq_nonneg (x-1)])
    (by refine ⟨1/2, by norm_num, by norm_num⟩)
  rw [integral_one_div_of_pos (by norm_num) (by norm_num)] at h
  norm_num only [show (3/2:ℝ)/(1/2)=3 by norm_num] at h
  have hi : (∫ x in (1/2:ℝ)..(3/2), 2-x)=(1:ℝ) := by
    rw [intervalIntegral.integral_sub (f:=fun x : ℝ => 2) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
    norm_num
  rwa [hi] at h

theorem strict_gap : (1/768:ℝ) < (1/72-Real.log 3/192)-13/2304 := by
  linarith [log_three_lt]

end
end QepReluIntegrals
