import QepFeedbackConditionalMoments
set_option maxHeartbeats 1800000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackMoments QepFeedbackConditionalMoments
namespace QepFeedbackAdaptive
noncomputable section


def q₁ (w₁ u₁ : ℝ) : ℝ := grid (w₁+u₁)-u₁
def n₁ (w₁ u₁ : ℝ) : ℝ := q₁ w₁ u₁-w₁

def adaptiveU₁₂ (w₁ u₁ : ℝ) : ℝ := n₁ w₁ u₁
def z₂ (w₁ w₂ u₁ : ℝ) : ℝ := w₂+(w₁-q₁ w₁ u₁)*adaptiveU₁₂ w₁ u₁
def q₂ (w₁ w₂ : ℝ) (u : ℝ × ℝ) : ℝ := grid (z₂ w₁ w₂ u.1+u.2)-u.2
def e₂ (w₁ w₂ : ℝ) (u : ℝ × ℝ) : ℝ := q₂ w₁ w₂ u-w₂
def pairInnovations (w₁ w₂ : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (n₁ w₁ u.1,innovation none (z₂ w₁ w₂ u.1) u.2)

theorem first_innovation_measurable (w₁ : ℝ) : Measurable (n₁ w₁) :=
  innovation_fixed_measurable none w₁

theorem second_target_measurable (w₁ w₂ : ℝ) : Measurable (z₂ w₁ w₂) := by
  have h := first_innovation_measurable w₁
  have heq : z₂ w₁ w₂ = fun u => w₂-(n₁ w₁ u)^2 := by
    funext u; unfold z₂ adaptiveU₁₂ n₁; ring
  rw [heq]
  exact measurable_const.sub (h.pow_const 2)

theorem actual_adaptive_joint_law (w₁ w₂ : ℝ) :
    MeasurePreserving (pairInnovations w₁ w₂) (noise.prod noise) (noise.prod noise) := by
  have hfirst : MeasurePreserving (n₁ w₁) noise noise :=
    ⟨first_innovation_measurable w₁,innovation_law none w₁⟩
  have ht : Measurable (fun p : ℝ × ℝ => z₂ w₁ w₂ p.1) :=
    (second_target_measurable w₁ w₂).comp measurable_fst
  have hm : Measurable (uncurry (fun u₁ u₂ => innovation none (z₂ w₁ w₂ u₁) u₂)) := by
    change Measurable (fun p : ℝ × ℝ => grid (z₂ w₁ w₂ p.1+p.2)-p.2-z₂ w₁ w₂ p.1)
    exact ((grid_measurable.comp (ht.add measurable_snd)).sub measurable_snd).sub ht
  exact hfirst.skew_product hm (Filter.Eventually.of_forall fun u₁ => innovation_law none (z₂ w₁ w₂ u₁))

theorem actual_adaptive_error_identity (w₁ w₂ : ℝ) (u : ℝ × ℝ) :
    e₂ w₁ w₂ u = (pairInnovations w₁ w₂ u).2-(pairInnovations w₁ w₂ u).1^2 := by
  unfold e₂ pairInnovations q₂ innovation reconstruct recenter z₂ adaptiveU₁₂ n₁
  ring


theorem actual_adaptive_second_error_mean (w₁ w₂ : ℝ) :
    (∫ u, e₂ w₁ w₂ u ∂noise.prod noise)=-(1/12:ℝ) := by
  have hg : Integrable (fun p : ℝ × ℝ => p.2-p.1^2) (noise.prod noise) :=
    (id_integrable.comp_snd noise).sub ((noise_integrable_power 2).comp_fst noise)
  simp_rw [actual_adaptive_error_identity]
  rw [integral_of_preserving (actual_adaptive_joint_law w₁ w₂) _ hg]
  rw [integral_sub (id_integrable.comp_snd noise) ((noise_integrable_power 2).comp_fst noise),
    integral_fun_snd (fun u : ℝ => u),integral_fun_fst (fun u : ℝ => u^2),noise_mean,noise_second_moment]
  simp

end
end QepFeedbackAdaptive
