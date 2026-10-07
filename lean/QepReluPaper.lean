import QepReluControls
open MeasureTheory Set
open QepFiniteDitherLaw QepReluProcess QepReluExpectation QepReluProbability
namespace QepReluPaper
noncomputable section


def paperNoise : Measure ℝ := volume.restrict (Ico (-(1/2:ℝ)) (1/2))

theorem paper_noise_eq : paperNoise=noise := restrict_Ico_eq_restrict_Ioc

theorem paper_base_expectation :
    (∫ d, (actualBase d)^2 ∂paperNoise.prod paperNoise)=(13/2304:ℝ) := by
  rw [paper_noise_eq]
  exact actual_base_loss

theorem paper_qep_expectation :
    (∫ d, (actualQep d)^2 ∂paperNoise.prod paperNoise)=(1/72-Real.log 3/192:ℝ) := by
  rw [paper_noise_eq]
  exact actual_qep_loss

theorem paper_probability_direction :
    (paperNoise.prod paperNoise).real {d | 0<actualQep d} <
    (paperNoise.prod paperNoise).real {d | 0<actualBase d} := by
  rw [paper_noise_eq]
  exact actual_less_often_positive

end
end QepReluPaper
