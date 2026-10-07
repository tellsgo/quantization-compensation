import QepReluExpectation
set_option maxHeartbeats 1000000
open MeasureTheory Set
open QepFiniteDitherLaw QepReluIntegrals QepReluProcess QepReluExpectation
namespace QepReluLegality
noncomputable section

def teacherOutput : ℝ := relu ((-(1/4:ℝ))*relu (1*1))

theorem teacher_zero : teacherOutput=0 := by norm_num [teacherOutput,relu]

theorem quantize_measurable (t : ℝ) : Measurable (quantize t) := by
  exact (grid_measurable.comp (measurable_const.add measurable_id)).sub measurable_id

theorem quantize_nonzero_ae (t : ℝ) : ∀ᵐ d ∂noise, quantize t d ≠ 0 := by
  have mp : MeasurePreserving (fun d => quantize t d-t) noise noise :=
    ⟨(quantize_measurable t).sub measurable_const,infinite_dither_law t⟩
  have hn : ∀ᵐ x ∂noise, x ≠ -t := by
    rw [ae_iff]
    simp only [not_not, ofPred_eq_eq_singleton]
    rw [noise,Measure.restrict_apply (measurableSet_singleton _)]
    exact measure_mono_null inter_subset_left (measure_singleton _)
  filter_upwards [mp.quasiMeasurePreserving.ae hn] with d hd
  intro h; exact hd (by rw [h]; ring)

theorem random_target_nonzero_ae (t : ℝ→ℝ) (ht : Measurable t) :
    ∀ᵐ d : ℝ×ℝ ∂noise.prod noise, quantize (t d.1) d.2 ≠ 0 := by
  have hm : Measurable (fun d : ℝ×ℝ => quantize (t d.1) d.2) := by
    unfold quantize
    exact (grid_measurable.comp ((ht.comp measurable_fst).add measurable_snd)).sub measurable_snd
  apply (Measure.ae_prod_iff_ae_ae (by exact (hm (measurableSet_singleton 0)).compl)).2
  exact Filter.Eventually.of_forall fun d => quantize_nonzero_ae (t d)

theorem actual_second_weights_nonzero_ae :
    ∀ᵐ d : ℝ×ℝ ∂noise.prod noise, qbase d ≠ 0 ∧ qqep d ≠ 0 := by
  filter_upwards [random_target_nonzero_ae (fun _ => -(1/4:ℝ)) measurable_const,
    random_target_nonzero_ae target target_measurable] with d hb hq
  exact ⟨hb,hq⟩

theorem actual_legal_ae : ∀ᵐ d : ℝ×ℝ ∂noise.prod noise,
    0 < (1:ℝ) ∧ 0 < first d.1*first d.1 ∧ quantize 1 d.1 ≠ 0 ∧ qbase d ≠ 0 ∧ qqep d ≠ 0 := by
  filter_upwards [actual_second_weights_nonzero_ae] with d hd
  exact ⟨by norm_num,input_gram_positive d.1,ne_of_gt (by linarith [(first_bounds d.1).1]),hd⟩

theorem actual_teacher_loss_gap : (1/768:ℝ) <
    (∫ d, (actualQep d-teacherOutput)^2 ∂noise.prod noise)-
    (∫ d, (actualBase d-teacherOutput)^2 ∂noise.prod noise) := by
  simp only [teacher_zero,sub_zero]
  exact actual_strict_gap

theorem one_layer_target_equal (w x : ℝ) : w+w*(x-x)*x/(x*x)=w := by ring

end
end QepReluLegality
