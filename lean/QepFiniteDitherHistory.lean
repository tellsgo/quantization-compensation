import QepFiniteDitherLaw
set_option maxHeartbeats 1000000
open MeasureTheory Set Function
open QepFiniteDitherLaw
namespace QepFiniteDitherHistory
noncomputable section



theorem history_joint_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (k : ℕ) (t : Ω → ℝ) (ht : Measurable t) :
    Measure.map (fun p : Ω × ℝ => (p.1,reconstruction k (t p.1) p.2-clip k (t p.1)))
      (μ.prod noise) = μ.prod noise := by
  have hm : Measurable (uncurry (fun ω u => reconstruction k (t ω) u-clip k (t ω))) := by
    change Measurable (fun p : Ω × ℝ => reconstruction k (t p.1) p.2-clip k (t p.1))
    unfold reconstruction quant clip
    exact ((measurable_const.max (measurable_const.min
      (grid_measurable.comp ((ht.comp measurable_fst).add measurable_snd)))).sub measurable_snd).sub
      (measurable_const.max (measurable_const.min (ht.comp measurable_fst)))
  exact ((MeasurePreserving.id μ).skew_product hm
    (Filter.Eventually.of_forall fun ω => finite_centered_dither_law k (t ω))).map_eq


theorem history_test_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (k : ℕ) (t : Ω → ℝ) (ht : Measurable t) (g : Ω × ℝ → ℝ)
    (hg : StronglyMeasurable g) :
    (∫ p : Ω × ℝ, g (p.1,reconstruction k (t p.1) p.2-clip k (t p.1)) ∂μ.prod noise) =
      ∫ p, g p ∂μ.prod noise := by
  have hm : Measurable (fun p : Ω × ℝ => (p.1,reconstruction k (t p.1) p.2-clip k (t p.1))) := by
    apply measurable_fst.prodMk
    unfold reconstruction quant clip
    exact ((measurable_const.max (measurable_const.min
      (grid_measurable.comp ((ht.comp measurable_fst).add measurable_snd)))).sub measurable_snd).sub
      (measurable_const.max (measurable_const.min (ht.comp measurable_fst)))
  have h := integral_map_of_stronglyMeasurable hm hg (μ:=μ.prod noise)
  rw [history_joint_law μ k t ht] at h
  exact h.symm

theorem finite_family_joint_law {ι : Type*} [Fintype ι] (k : ℕ) (t : ι → ℝ) :
    Measure.map (fun u i => reconstruction k (t i) (u i)-clip k (t i))
      (Measure.pi (fun _ : ι => noise)) = Measure.pi (fun _ : ι => noise) := by
  exact (measurePreserving_pi (fun _ : ι => noise) (fun _ : ι => noise)
    (fun i => ⟨(reconstruction_measurable k (t i)).sub measurable_const,
      finite_centered_dither_law k (t i)⟩)).map_eq


theorem history_finite_family_joint_law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [SFinite μ] (k : ℕ) (t : Ω → ι → ℝ) (ht : Measurable t) :
    Measure.map (fun p : Ω × (ι → ℝ) =>
      (p.1,fun i => reconstruction k (t p.1 i) (p.2 i)-clip k (t p.1 i)))
      (μ.prod (Measure.pi (fun _ : ι => noise))) = μ.prod (Measure.pi (fun _ : ι => noise)) := by
  have hm : Measurable (uncurry (fun (ω : Ω) (u : ι → ℝ) i => reconstruction k (t ω i) (u i)-clip k (t ω i))) := by
    apply measurable_pi_iff.mpr
    intro i
    have hti : Measurable (fun p : Ω × (ι → ℝ) => t p.1 i) := (measurable_pi_apply i).comp (ht.comp measurable_fst)
    have hui : Measurable (fun p : Ω × (ι → ℝ) => p.2 i) := (measurable_pi_apply i).comp measurable_snd
    unfold reconstruction quant clip
    exact ((measurable_const.max (measurable_const.min
      (grid_measurable.comp (hti.add hui)))).sub hui).sub
      (measurable_const.max (measurable_const.min hti))
  exact ((MeasurePreserving.id μ).skew_product hm
    (Filter.Eventually.of_forall fun ω => finite_family_joint_law k (t ω))).map_eq

end
end QepFiniteDitherHistory
