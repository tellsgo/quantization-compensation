import QepFiniteDitherMatrix
set_option maxHeartbeats 1400000
set_option linter.unusedVariables false
open MeasureTheory
namespace QepOverloadGap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
def energy (x : H) : ℝ := inner ℝ x x
def cross (x y : H) : ℝ := inner ℝ x y

theorem energy_norm (x : H) : energy x=‖x‖^2 := real_inner_self_eq_norm_sq x
 theorem energy_nonneg (x : H) : 0≤energy x := by rw [energy_norm]; positivity
 theorem cross_symm (x y : H) : cross x y=cross y x := (real_inner_comm x y).symm

def residual (A S J : H) (α : ℝ) := A-α • S-J

theorem general_gap (A S J J₀ : H) (α : ℝ) :
    energy (residual A S J α)-energy (A-J₀) =
      α^2*energy S-2*α*cross A S-2*cross (A-α • S) J+energy J+
      2*cross A J₀-energy J₀ := by
  simp only [energy,residual,cross,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm S A,real_inner_comm J A,real_inner_comm J S,real_inner_comm J₀ A]
  ring

theorem projected_gap (A S J J₀ : H) (α : ℝ) (hp : cross A S=energy S) :
    energy (residual A S J α)-energy (A-J₀) =
      -α*(2-α)*energy S-2*cross (A-α • S) J+energy J+
      2*cross A J₀-energy J₀ := by
  rw [general_gap,hp]; ring

theorem cross_sqrt_bound (x y : H) : |cross x y|≤Real.sqrt (energy x*energy y) := by
  rw [energy_norm,energy_norm,Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm x y

theorem four_term_bound (p q u v : ℝ) (hu : 0≤u) (hv : 0≤v) :
    |-2*p+u+2*q-v|≤2*|p|+u+2*|q|+v := by
  calc
    _ ≤ |-2*p+u+2*q|+|v| := abs_sub _ _
    _ ≤ (|-2*p+u|+|2*q|)+|v| := by gcongr; exact abs_add_le _ _
    _ ≤ (|-2*p|+|u|+|2*q|)+|v| := by gcongr; exact abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg hu,abs_of_nonneg hv]; norm_num

theorem general_gap_bound (A S J J₀ : H) (α : ℝ) :
    |energy (residual A S J α)-energy (A-J₀) -
      (α^2*energy S-2*α*cross A S)| ≤
      2*Real.sqrt (energy (A-α • S)*energy J)+energy J+
      2*Real.sqrt (energy A*energy J₀)+energy J₀ := by
  rw [general_gap]
  have he : α^2*energy S-2*α*cross A S-2*cross (A-α • S) J+energy J+
      2*cross A J₀-energy J₀-(α^2*energy S-2*α*cross A S) =
      -2*cross (A-α • S) J+energy J+2*cross A J₀-energy J₀ := by ring
  rw [he]
  exact (four_term_bound _ _ _ _ (energy_nonneg _) (energy_nonneg _)).trans (by
    gcongr <;> apply cross_sqrt_bound)

theorem projected_gap_bound (A S J J₀ : H) (α : ℝ) (hp : cross A S=energy S) :
    |energy (residual A S J α)-energy (A-J₀)+α*(2-α)*energy S| ≤
      2*Real.sqrt (energy (A-α • S)*energy J)+energy J+
      2*Real.sqrt (energy A*energy J₀)+energy J₀ := by
  have h := general_gap_bound A S J J₀ α
  rw [hp] at h
  convert h using 1 <;> congr 1 <;> ring

theorem sufficient_improvement (A S J J₀ : H) (α : ℝ)
    (hp : cross A S=energy S)
    (hgain : 2*Real.sqrt (energy (A-α • S)*energy J)+energy J+
      2*Real.sqrt (energy A*energy J₀)+energy J₀ ≤ α*(2-α)*energy S) :
    energy (residual A S J α)≤energy (A-J₀) := by
  have hb := (projected_gap_bound A S J J₀ α hp).trans hgain
  have hu := le_abs_self (energy (residual A S J α)-energy (A-J₀)+α*(2-α)*energy S)
  linarith


theorem l2_cross_sqrt_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω)
    (S J : Lp E 2 μ) :
    |∫ ω, inner ℝ (S ω) (J ω) ∂μ| ≤
      Real.sqrt ((∫ ω, ‖S ω‖^2 ∂μ)*(∫ ω, ‖J ω‖^2 ∂μ)) := by
  have hb := cross_sqrt_bound S J
  simpa only [cross,energy,L2.inner_def,real_inner_self_eq_norm_sq] using hb


theorem memLp_cross_sqrt_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω)
    (S J : Ω → E) (hS : MemLp S 2 μ) (hJ : MemLp J 2 μ) :
    |∫ ω, inner ℝ (S ω) (J ω) ∂μ| ≤
      Real.sqrt ((∫ ω, ‖S ω‖^2 ∂μ)*(∫ ω, ‖J ω‖^2 ∂μ)) := by
  have hb := l2_cross_sqrt_bound μ (hS.toLp S) (hJ.toLp J)
  have hc : (∫ ω, inner ℝ ((hS.toLp S) ω) ((hJ.toLp J) ω) ∂μ) =
      ∫ ω, inner ℝ (S ω) (J ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hS.coeFn_toLp,hJ.coeFn_toLp] with ω h1 h2
    rw [h1,h2]
  have hs : (∫ ω, ‖(hS.toLp S) ω‖^2 ∂μ)=∫ ω, ‖S ω‖^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hS.coeFn_toLp] with ω h; rw [h]
  have hj : (∫ ω, ‖(hJ.toLp J) ω‖^2 ∂μ)=∫ ω, ‖J ω‖^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hJ.coeFn_toLp] with ω h; rw [h]
  rwa [hc,hs,hj] at hb

theorem overload_event_cross_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω)
    (S J : Ω → E) (hS : MemLp S 2 μ) (hJ : MemLp J 2 μ)
    (O : Set Ω) (hO : MeasurableSet O) (hzero : ∀ᵐ ω ∂μ, ω ∉ O → J ω=0) :
    |∫ ω, inner ℝ (S ω) (J ω) ∂μ| ≤
      Real.sqrt ((∫ ω in O, ‖S ω‖^2 ∂μ)*(∫ ω, ‖J ω‖^2 ∂μ)) := by
  have hb := memLp_cross_sqrt_bound μ (O.indicator S) J (hS.indicator hO) hJ
  have hc : (∫ ω, inner ℝ (O.indicator S ω) (J ω) ∂μ)=
      ∫ ω, inner ℝ (S ω) (J ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hzero] with ω h
    by_cases ho : ω∈O
    · simp [Set.indicator_of_mem ho]
    · simp [Set.indicator_of_notMem ho,h ho]
  have he : (fun ω => ‖O.indicator S ω‖^2) = O.indicator (fun ω => ‖S ω‖^2) := by
    funext ω; by_cases ho : ω∈O <;> simp [ho]
  rw [hc,he,integral_indicator hO] at hb
  exact hb

end
end QepOverloadGap
