import Mathlib

set_option maxHeartbeats 1400000
set_option linter.unusedVariables false

open Set MeasureTheory Function
open scoped ENNReal

namespace QepFiniteDitherLaw
noncomputable section


def noise : Measure ℝ := volume.restrict (Ioc (-(1/2:ℝ)) (1/2))

def wrap (x : ℝ) : ℝ := toIocMod (by norm_num : (0:ℝ)<1) (-(1/2:ℝ)) x


def grid (x : ℝ) : ℝ := (round x : ℝ)

def clip (k : ℕ) (x : ℝ) : ℝ := max 0 (min (k:ℝ) x)


def quant (k : ℕ) (x : ℝ) : ℝ := clip k (grid x)

def reconstruction (k : ℕ) (t u : ℝ) : ℝ := quant k (t+u)-u

theorem grid_error_wrap (x : ℝ) : grid x-x=wrap (-x) := by
  symm
  apply (toIocMod_eq_iff (by norm_num : (0:ℝ)<1)).mpr
  refine ⟨?_, -(round x), ?_⟩
  · have hl := sub_half_lt_round x
    have hu := round_le_add_half x
    dsimp [grid]
    constructor <;> linarith
  · simp [grid]; ring

theorem wrap_measurable : Measurable wrap := by
  change Measurable (fun x : ℝ => ((AddCircle.equivIoc 1 (-(1/2:ℝ)))
    (x : UnitAddCircle)).val)
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc 1 (-(1/2:ℝ))).measurable.comp AddCircle.measurable_mk')

theorem grid_measurable : Measurable grid := by
  have h : grid = fun x => x + wrap (-x) := by
    funext x; linarith [grid_error_wrap x]
  rw [h]
  exact measurable_id.add (wrap_measurable.comp measurable_neg)

theorem reconstruction_measurable (k : ℕ) (t : ℝ) : Measurable (reconstruction k t) := by
  unfold reconstruction quant clip
  exact (measurable_const.max (measurable_const.min
    (grid_measurable.comp (measurable_const.add measurable_id)))).sub measurable_id

theorem wrap_shift_measurePreserving (t : ℝ) :
    MeasurePreserving (fun u : ℝ => wrap (-(t+u))) noise noise := by
  have circle := (Measure.measurePreserving_neg (volume : Measure UnitAddCircle)).comp
    ((measurePreserving_add_left (volume : Measure UnitAddCircle) (t : UnitAddCircle)).comp
      (UnitAddCircle.measurePreserving_mk (-(1/2:ℝ))))
  have lift := (measurePreserving_subtype_coe
      (measurableSet_Ioc : MeasurableSet (Ioc (-(1/2:ℝ)) (-(1/2:ℝ)+1)))).comp
      (AddCircle.measurePreserving_equivIoc 1 (a:=-(1/2:ℝ)))
  convert lift.comp circle using 1 <;> try { norm_num [noise] }
  funext u
  change wrap (-(t+u)) = ((AddCircle.equivIoc 1 (-(1/2:ℝ)))
    (-((t:UnitAddCircle)+(u:UnitAddCircle)))).val
  rw [← AddCircle.coe_add, ← AddCircle.coe_neg]
  rfl

theorem infinite_dither_law (t : ℝ) :
    Measure.map (fun u => grid (t+u)-u-t) noise = noise := by
  have h : (fun u => grid (t+u)-u-t) = fun u => wrap (-(t+u)) := by
    funext u; linarith [grid_error_wrap (t+u)]
  rw [h]
  exact (wrap_shift_measurePreserving t).map_eq

theorem noise_neg : Measure.map (fun u : ℝ => -u) noise = noise := by
  have hz : ∀ᵐ u ∂noise, grid u=0 := by
    have hm : noise = volume.restrict (Ioo (-(1/2:ℝ)) (1/2)) := by
      exact restrict_Ioo_eq_restrict_Ioc.symm
    rw [hm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hr : round u=0 := round_eq_zero_iff.mpr ⟨le_of_lt hu.1,hu.2⟩
    simp [grid,hr]
  have h : (fun u => grid (0+u)-u-0) =ᵐ[noise] (fun u => -u) := by
    filter_upwards [hz] with u hu; simp [hu]
  rw [← Measure.map_congr h]
  exact infinite_dither_law 0

theorem grid_bounds_inside (k : ℕ) {t u : ℝ} (ht0 : 0 ≤ t) (htk : t ≤ k)
    (hu : u ∈ Ioo (-(1/2:ℝ)) (1/2)) : 0 ≤ grid (t+u) ∧ grid (t+u) ≤ k := by
  have hl := sub_half_lt_round (t+u)
  have hh := round_le_add_half (t+u)
  have hli : (-1:ℝ) < (round (t+u):ℝ) := by linarith [hu.1]
  have hui : (round (t+u):ℝ) < (k:ℝ)+1 := by linarith [hu.2]
  have hli' : (-1:ℤ) < round (t+u) := by exact_mod_cast hli
  have hui' : round (t+u) < (k:ℤ)+1 := by exact_mod_cast hui
  have hlo : (0:ℤ) ≤ round (t+u) := by omega
  have hup : round (t+u) ≤ (k:ℤ) := by omega
  constructor <;> dsimp [grid] <;> exact_mod_cast (by assumption)

theorem quant_inside (k : ℕ) {t u : ℝ} (ht0 : 0 ≤ t) (htk : t ≤ k)
    (hu : u ∈ Ioo (-(1/2:ℝ)) (1/2)) : quant k (t+u)=grid (t+u) := by
  obtain ⟨h0,hk⟩ := grid_bounds_inside k ht0 htk hu
  simp [quant,clip,min_eq_right hk,max_eq_right h0]

theorem quant_below (k : ℕ) {t u : ℝ} (ht : t ≤ 0)
    (hu : u ∈ Ioo (-(1/2:ℝ)) (1/2)) : quant k (t+u)=0 := by
  have h : (round (t+u):ℝ) < 1 := by linarith [round_le_add_half (t+u),hu.2]
  have hi : round (t+u) < (1:ℤ) := by exact_mod_cast h
  have hi0 : round (t+u) ≤ (0:ℤ) := by omega
  have hg : grid (t+u) ≤ 0 := by dsimp [grid]; exact_mod_cast hi0
  simp [quant,clip,min_eq_right (hg.trans (Nat.cast_nonneg k)),max_eq_left hg]

theorem quant_above (k : ℕ) {t u : ℝ} (ht : (k:ℝ) ≤ t)
    (hu : u ∈ Ioo (-(1/2:ℝ)) (1/2)) : quant k (t+u)=k := by
  have h : (k:ℝ)-1 < (round (t+u):ℝ) := by linarith [sub_half_lt_round (t+u),hu.1]
  have hi : (k:ℤ)-1 < round (t+u) := by exact_mod_cast h
  have hki : (k:ℤ) ≤ round (t+u) := by omega
  have hk : (k:ℝ) ≤ grid (t+u) := by dsimp [grid]; exact_mod_cast hki
  simp [quant,clip,min_eq_left hk]

theorem finite_centered_dither_law (k : ℕ) (t : ℝ) :
    Measure.map (fun u => reconstruction k t u - clip k t) noise = noise := by
  have hu : ∀ᵐ u ∂noise, u ∈ Ioo (-(1/2:ℝ)) (1/2) := by
    have hm : noise = volume.restrict (Ioo (-(1/2:ℝ)) (1/2)) :=
      restrict_Ioo_eq_restrict_Ioc.symm
    rw [hm]; exact ae_restrict_mem measurableSet_Ioo
  rcases le_total t 0 with ht | ht
  · have hc : clip k t=0 := by
      simp [clip,min_eq_right (ht.trans (Nat.cast_nonneg k)),max_eq_left ht]
    have heq : (fun u => reconstruction k t u-clip k t) =ᵐ[noise] (fun u => -u) := by
      filter_upwards [hu] with u hu
      simp [reconstruction,quant_below k ht hu,hc]
    rw [Measure.map_congr heq]; exact noise_neg
  · rcases le_total (k:ℝ) t with hk | hk
    · have hc : clip k t=k := by simp [clip,min_eq_left hk]
      have heq : (fun u => reconstruction k t u-clip k t) =ᵐ[noise] (fun u => -u) := by
        filter_upwards [hu] with u hu
        simp [reconstruction,quant_above k hk hu,hc]
      rw [Measure.map_congr heq]; exact noise_neg
    · have hc : clip k t=t := by simp [clip,min_eq_right hk,max_eq_right ht]
      have heq : (fun u => reconstruction k t u-clip k t) =ᵐ[noise]
          (fun u => grid (t+u)-u-t) := by
        filter_upwards [hu] with u hu
        simp [reconstruction,quant_inside k ht hk hu,hc]
      rw [Measure.map_congr heq]; exact infinite_dither_law t

theorem quant_is_codepoint (k : ℕ) (x : ℝ) :
    ∃ n : ℤ, 0 ≤ n ∧ n ≤ (k:ℤ) ∧ quant k x=(n:ℝ) := by
  refine ⟨max 0 (min (k:ℤ) (round x)),le_max_left _ _,?_,?_⟩
  · exact max_le (by omega) (min_le_left _ _)
  · simp [quant,clip,grid]

theorem quant_is_nearest (k : ℕ) (x : ℝ) (n : ℤ) (hn0 : 0 ≤ n) (hnk : n ≤ k) :
    |x-quant k x| ≤ |x-(n:ℝ)| := by
  have hg := round_le x n
  have h0 : (0:ℝ) ≤ n := by exact_mod_cast hn0
  have hk : (n:ℝ) ≤ k := by exact_mod_cast hnk
  by_cases hlo : grid x ≤ 0
  · have hq : quant k x=0 := by
      simp [quant,clip,min_eq_right (hlo.trans (Nat.cast_nonneg k)),max_eq_left hlo]
    rw [hq]
    by_cases hx : x ≤ 0
    · rw [sub_zero,abs_of_nonpos hx,abs_of_nonpos (by linarith : x-(n:ℝ) ≤ 0)]
      linarith
    · have hxr : 0 ≤ x-grid x := by linarith
      have hh : |x| ≤ |x-grid x| := by
        rw [abs_of_nonneg (le_of_not_ge hx),abs_of_nonneg hxr]; linarith
      simpa [grid] using hh.trans hg
  · by_cases hhi : (k:ℝ) ≤ grid x
    · have hq : quant k x=k := by simp [quant,clip,min_eq_left hhi]
      rw [hq]
      by_cases hx : (k:ℝ) ≤ x
      · rw [abs_of_nonneg (by linarith : 0 ≤ x-(k:ℝ)),abs_of_nonneg (by linarith : 0 ≤ x-(n:ℝ))]
        linarith
      · have hh : |x-(k:ℝ)| ≤ |x-grid x| := by
          rw [abs_of_nonpos (by linarith : x-(k:ℝ) ≤ 0),abs_of_nonpos (by linarith : x-grid x ≤ 0)]
          linarith
        simpa [grid] using hh.trans hg
    · have hq : quant k x=grid x := by
        simp [quant,clip,min_eq_right (le_of_not_ge hhi),max_eq_right (le_of_not_ge hlo)]
      simpa [hq,grid] using hg

instance noise_probability : IsProbabilityMeasure noise := by
  constructor
  norm_num [noise,Measure.restrict_apply,Real.volume_Ioc]

theorem centered_integral (k : ℕ) (t : ℝ) (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ u, g (reconstruction k t u-clip k t) ∂noise) = ∫ v, g v ∂noise := by
  have h := integral_map_of_stronglyMeasurable (φ:=fun u => reconstruction k t u-clip k t)
    ((reconstruction_measurable k t).sub measurable_const) hg (μ:=noise)
  rw [finite_centered_dither_law] at h
  exact h.symm

theorem noise_integrable_power (n : ℕ) : Integrable (fun u : ℝ => u^n) noise := by
  exact ((continuous_id.pow n).integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem centered_integrable_power (k n : ℕ) (t : ℝ) :
    Integrable (fun u => (reconstruction k t u-clip k t)^n) noise := by
  have h : Integrable (fun u : ℝ => u^n)
      (Measure.map (fun u => reconstruction k t u-clip k t) noise) := by
    rw [finite_centered_dither_law]; exact noise_integrable_power n
  exact (integrable_map_measure (continuous_id.pow n).aestronglyMeasurable
    ((reconstruction_measurable k t).sub measurable_const).aemeasurable).mp h

theorem noise_mean : (∫ u : ℝ, u ∂noise)=0 := by
  change (∫ u : ℝ in Ioc (-(1/2:ℝ)) (1/2),u)=0
  rw [← intervalIntegral.integral_of_le (by norm_num : (-(1/2:ℝ))≤1/2),integral_id]
  norm_num

theorem noise_second_moment : (∫ u : ℝ, u^2 ∂noise)=1/12 := by
  change (∫ u : ℝ in Ioc (-(1/2:ℝ)) (1/2),u^2)=1/12
  rw [← intervalIntegral.integral_of_le (by norm_num : (-(1/2:ℝ))≤1/2),integral_pow]
  norm_num

theorem centered_mean (k : ℕ) (t : ℝ) :
    (∫ u, reconstruction k t u-clip k t ∂noise)=0 := by
  exact (centered_integral k t id (by fun_prop)).trans noise_mean

theorem centered_second_moment (k : ℕ) (t : ℝ) :
    (∫ u, (reconstruction k t u-clip k t)^2 ∂noise)=1/12 := by
  exact (centered_integral k t (fun x=>x^2) (by fun_prop)).trans noise_second_moment

theorem affine_centered_square (k : ℕ) (t a b : ℝ) :
    (∫ u, (a+b*(reconstruction k t u-clip k t))^2 ∂noise) = a^2+b^2/12 := by
  have hi : Integrable (fun u=>reconstruction k t u-clip k t) noise := by
    simpa using centered_integrable_power k 1 t
  have hi2 := centered_integrable_power k 2 t
  have hexp : (fun u => (a+b*(reconstruction k t u-clip k t))^2) =
      (fun u => a^2+(2*a*b)*(reconstruction k t u-clip k t)+b^2*(reconstruction k t u-clip k t)^2) := by
    funext u; ring
  have hadd : Integrable (fun u => a^2+(2*a*b)*(reconstruction k t u-clip k t)) noise :=
    (integrable_const (a^2)).add (hi.const_mul (2*a*b))
  rw [hexp,integral_add hadd (hi2.const_mul (b^2)),
    integral_add (integrable_const (a^2)) (hi.const_mul (2*a*b)),integral_const_mul,integral_const_mul,
    centered_mean,centered_second_moment]
  simp; ring

theorem actual_scalar_mean (k : ℕ) (t : ℝ) :
    (∫ u, reconstruction k t u-t ∂noise)=clip k t-t := by
  have hi : Integrable (fun u=>reconstruction k t u-clip k t) noise := by
    simpa using centered_integrable_power k 1 t
  have hexp : (fun u => reconstruction k t u-t) =
      (fun u => (reconstruction k t u-clip k t)+(clip k t-t)) := by funext u; ring
  rw [hexp,integral_add hi (integrable_const _),centered_mean]
  simp

theorem actual_scalar_mse (k : ℕ) (t : ℝ) :
    (∫ u, (reconstruction k t u-t)^2 ∂noise)=1/12+(clip k t-t)^2 := by
  calc
    _ = ∫ u, ((clip k t-t)+1*(reconstruction k t u-clip k t))^2 ∂noise := by
      congr 1; funext u; ring
    _ = (clip k t-t)^2+1^2/12 := affine_centered_square k t (clip k t-t) 1
    _ = _ := by ring


def scaledQuant (a Δ : ℝ) (k : ℕ) (x : ℝ) := a+Δ*quant k ((x-a)/Δ)
def scaledClip (a Δ : ℝ) (k : ℕ) (t : ℝ) := a+Δ*clip k ((t-a)/Δ)
def scaledReconstruction (a Δ : ℝ) (k : ℕ) (t u : ℝ) :=
  scaledQuant a Δ k (t+Δ*u)-Δ*u

theorem scaled_reconstruction_identity (a Δ : ℝ) (hΔ : Δ ≠ 0) (k : ℕ) (t u : ℝ) :
    scaledReconstruction a Δ k t u-scaledClip a Δ k t =
      Δ*(reconstruction k ((t-a)/Δ) u-clip k ((t-a)/Δ)) := by
  have h : (t+Δ*u-a)/Δ=(t-a)/Δ+u := by field_simp; ring
  simp only [scaledReconstruction,scaledQuant,scaledClip,h,reconstruction]
  ring

theorem scaled_continuous_dither_law (a Δ : ℝ) (hΔ : 0 < Δ) (k : ℕ) (t : ℝ) :
    Measure.map (fun u => scaledReconstruction a Δ k t u-scaledClip a Δ k t) noise =
      Measure.map (fun v => Δ*v) noise := by
  have h : (fun u => scaledReconstruction a Δ k t u-scaledClip a Δ k t) =
      (fun v => Δ*v) ∘ (fun u => reconstruction k ((t-a)/Δ) u-clip k ((t-a)/Δ)) := by
    funext u; exact scaled_reconstruction_identity a Δ (ne_of_gt hΔ) k t u
  have hm : Measurable (fun u => reconstruction k ((t-a)/Δ) u-clip k ((t-a)/Δ)) :=
    (reconstruction_measurable k ((t-a)/Δ)).sub measurable_const
  rw [h,← Measure.map_map (g:=fun v=>Δ*v) (by fun_prop) hm,finite_centered_dither_law]

theorem scaled_clip_is_interval_clip (a Δ : ℝ) (hΔ : 0 < Δ) (k : ℕ) (t : ℝ) :
    scaledClip a Δ k t = max a (min (a+Δ*k) t) := by
  unfold scaledClip clip
  rw [mul_max_of_nonneg _ _ (le_of_lt hΔ),mul_min_of_nonneg _ _ (le_of_lt hΔ)]
  have h : Δ*((t-a)/Δ)=t-a := by field_simp
  rw [h]
  simp only [mul_zero]
  rw [add_max,add_zero,add_min,add_sub_cancel]

end
end QepFiniteDitherLaw
