import QepFiniteDitherHistory
set_option maxHeartbeats 1600000
open MeasureTheory Set Function
open QepFiniteDitherLaw
namespace QepFeedbackInnovation
noncomputable section


def recenter (mode : Option ℕ) (t : ℝ) : ℝ :=
  match mode with | none => t | some k => clip k t

def reconstruct (mode : Option ℕ) (t u : ℝ) : ℝ :=
  match mode with | none => grid (t+u)-u | some k => reconstruction k t u

def innovation (mode : Option ℕ) (t u : ℝ) : ℝ :=
  reconstruct mode t u - recenter mode t

theorem innovation_measurable (mode : Option ℕ) :
    Measurable (fun p : ℝ × ℝ => innovation mode p.1 p.2) := by
  cases mode with
  | none => exact ((grid_measurable.comp (measurable_fst.add measurable_snd)).sub measurable_snd).sub measurable_fst
  | some k =>
    unfold innovation reconstruct recenter reconstruction quant clip
    exact ((measurable_const.max (measurable_const.min
      (grid_measurable.comp (measurable_fst.add measurable_snd)))).sub measurable_snd).sub
      (measurable_const.max (measurable_const.min measurable_fst))

theorem innovation_law (mode : Option ℕ) (t : ℝ) :
    Measure.map (innovation mode t) noise = noise := by
  cases mode with
  | none => exact infinite_dither_law t
  | some k => exact finite_centered_dither_law k t


theorem complete_history_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (mode : Option ℕ) (t : Ω → ℝ) (ht : Measurable t) :
    MeasurePreserving (fun p : Ω × ℝ => (p.1,innovation mode (t p.1) p.2))
      (μ.prod noise) (μ.prod noise) := by
  have hp : Measurable (fun p : Ω × ℝ => (t p.1,p.2)) :=
    (ht.comp measurable_fst).prodMk measurable_snd
  have hm : Measurable (uncurry (fun ω u => innovation mode (t ω) u)) := by
    change Measurable ((fun p : ℝ × ℝ => innovation mode p.1 p.2) ∘ (fun p : Ω × ℝ => (t p.1,p.2)))
    exact (innovation_measurable mode).comp hp
  exact (MeasurePreserving.id μ).skew_product hm (Filter.Eventually.of_forall fun ω => innovation_law mode (t ω))

theorem innovation_fixed_measurable (mode : Option ℕ) (t : ℝ) :
    Measurable (innovation mode t) := by
  cases mode with
  | none => exact ((grid_measurable.comp (measurable_const.add measurable_id)).sub measurable_id).sub measurable_const
  | some k => exact (reconstruction_measurable k t).sub measurable_const

theorem innovation_integral (mode : Option ℕ) (t : ℝ) (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ u, g (innovation mode t u) ∂noise) = ∫ v, g v ∂noise := by
  have h := integral_map_of_stronglyMeasurable (μ:=noise) (innovation_fixed_measurable mode t) hg
  rw [innovation_law] at h
  exact h.symm

theorem innovation_integrable_power (mode : Option ℕ) (t : ℝ) (n : ℕ) :
    Integrable (fun u => (innovation mode t u)^n) noise := by
  have mp : MeasurePreserving (innovation mode t) noise noise :=
    ⟨innovation_fixed_measurable mode t,innovation_law mode t⟩
  exact mp.integrable_comp_of_integrable (noise_integrable_power n)

theorem innovation_mean (mode : Option ℕ) (t : ℝ) :
    (∫ u, innovation mode t u ∂noise)=0 :=
  (innovation_integral mode t id (by fun_prop)).trans noise_mean

theorem innovation_second (mode : Option ℕ) (t : ℝ) :
    (∫ u, (innovation mode t u)^2 ∂noise)=1/12 :=
  (innovation_integral mode t (fun x => x^2) (by fun_prop)).trans noise_second_moment


def History : ℕ → Type
  | 0 => Unit
  | n+1 => History n × ℝ

instance historyMeasurable : (n : ℕ) → MeasurableSpace (History n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => MeasurableSpace.prod (historyMeasurable n) inferInstance

def historyNoise : (n : ℕ) → Measure (History n)
  | 0 => Measure.dirac ()
  | n+1 => (historyNoise n).prod noise

instance historyProbability (n : ℕ) : IsProbabilityMeasure (historyNoise n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih => exact inferInstanceAs (IsProbabilityMeasure ((historyNoise n).prod noise))


def causalInnovations (mode : ℕ → Option ℕ) (target : (n : ℕ) → History n → ℝ) :
    (n : ℕ) → History n → History n
  | 0 => id
  | n+1 => fun p => (causalInnovations mode target n p.1,innovation (mode n) (target n p.1) p.2)


theorem causal_innovations_measurePreserving (mode : ℕ → Option ℕ)
    (target : (n : ℕ) → History n → ℝ) (ht : ∀ n, Measurable (target n)) (n : ℕ) :
    MeasurePreserving (causalInnovations mode target n) (historyNoise n) (historyNoise n) := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    have hs := complete_history_law (historyNoise n) (mode n) (target n) (ht n)
    have hp := ih.prod (MeasurePreserving.id noise)
    exact hp.comp hs

theorem causal_innovations_joint_law (mode : ℕ → Option ℕ)
    (target : (n : ℕ) → History n → ℝ) (ht : ∀ n, Measurable (target n)) (n : ℕ) :
    Measure.map (causalInnovations mode target n) (historyNoise n) = historyNoise n :=
  (causal_innovations_measurePreserving mode target ht n).map_eq

end
end QepFeedbackInnovation
