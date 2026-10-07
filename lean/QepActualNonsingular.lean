import QepFiniteOverloadExamples
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
open MeasureTheory MeasureTheory.Measure Set QepFiniteDitherLaw QepFiniteDitherMatrix
namespace QepActualNonsingular
noncomputable section
attribute [local fun_prop] QepFiniteDitherLaw.reconstruction_measurable

theorem reconstruction_ae_ne (k : ℕ) (t x : ℝ) :
    ∀ᵐ u ∂noise, reconstruction k t u ≠ x := by
  have hn : ∀ᵐ u ∂noise, u ≠ x-clip k t := by
    exact ae_restrict_of_ae (volume.ae_ne (x-clip k t))
  have hm := finite_centered_dither_law k t
  rw [← hm] at hn
  have he := ae_of_ae_map ((reconstruction_measurable k t).sub measurable_const).aemeasurable hn
  filter_upwards [he] with u hu
  exact fun h => hu (by change reconstruction k t u-clip k t=x-clip k t; rw [h])

def detExpr (k : ℕ) (T : Mat) (u : Pair × Pair) :=
  reconstruction k (T 0 0) u.1.1*reconstruction k (T 1 1) u.2.2-
  reconstruction k (T 0 1) u.1.2*reconstruction k (T 1 0) u.2.1

theorem detExpr_measurable (k : ℕ) (T : Mat) : Measurable (detExpr k T) := by
  unfold detExpr; fun_prop

theorem reconstructed_ae_det_ne_zero (k : ℕ) (T : Mat) :
    ∀ᵐ u ∂fourNoise, (reconstructed k T u).det ≠ 0 := by
  have hs : MeasurableSet {u : Pair × Pair | detExpr k T u ≠ 0} :=
    (measurableSet_eq_fun (detExpr_measurable k T) measurable_const).compl
  have hfirst : ∀ᵐ v : Pair ∂rowNoise, reconstruction k (T 0 0) v.1 ≠ 0 := by
    apply (ae_prod_iff_ae_ae ((measurableSet_eq_fun ((reconstruction_measurable k (T 0 0)).comp measurable_fst) measurable_const).compl)).mpr
    filter_upwards [reconstruction_ae_ne k (T 0 0) 0] with v hv
    exact Filter.Eventually.of_forall (fun _ => hv)
  have hdet : ∀ᵐ u ∂fourNoise, detExpr k T u ≠ 0 := by
    apply (ae_prod_iff_ae_ae hs).mpr
    filter_upwards [hfirst] with u hu
    have hm : MeasurableSet {v : Pair | detExpr k T (u,v) ≠ 0} := by
      exact (measurableSet_eq_fun ((detExpr_measurable k T).comp (measurable_const.prodMk measurable_id)) measurable_const).compl
    apply (ae_prod_iff_ae_ae hm).mpr
    apply Filter.Eventually.of_forall; intro v
    filter_upwards [reconstruction_ae_ne k (T 1 1)
      (reconstruction k (T 0 1) u.2*reconstruction k (T 1 0) v/reconstruction k (T 0 0) u.1)] with w hw
    intro hd
    apply hw
    apply (eq_div_iff hu).mpr
    dsimp [detExpr] at hd
    nlinarith [hd]
  filter_upwards [hdet] with u hu
  simpa [detExpr,reconstructed,Matrix.det_fin_two] using hu

theorem reconstructed_ae_isUnit_det (k : ℕ) (T : Mat) :
    ∀ᵐ u ∂fourNoise, IsUnit (reconstructed k T u).det := by
  filter_upwards [reconstructed_ae_det_ne_zero k T] with u hu
  exact isUnit_iff_ne_zero.mpr hu

theorem example1_fixed_alpha_ae_legal (α : ℝ) :
    ∀ᵐ u ∂fourNoise, IsUnit (reconstructed 3
      (QepFiniteOverloadExamples.target QepFiniteOverloadExamples.W₁
        QepFiniteOverloadExamples.X₁ QepFiniteOverloadExamples.Z₁ α) u).det :=
  reconstructed_ae_isUnit_det 3 _


theorem example2_fixed_alpha_ae_legal (α : ℝ) :
    ∀ᵐ u ∂fourNoise, IsUnit (reconstructed 3
      (QepFiniteOverloadExamples.target QepFiniteOverloadExamples.W₂
        QepFiniteOverloadExamples.X₂ QepFiniteOverloadExamples.Z₂ α) u).det :=
  reconstructed_ae_isUnit_det 3 _
end
end QepActualNonsingular
