import QepFeedbackProcess
set_option maxHeartbeats 1600000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess
namespace QepFeedbackUpstream
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]


theorem causal_innovations_joint_measurable (mode : ℕ → Option ℕ)
    (t : Ω → (n : ℕ) → History n → ℝ)
    (ht : ∀ n, Measurable (fun p : Ω × History n => t p.1 n p.2)) (n : ℕ) :
    Measurable (fun p : Ω × History n => causalInnovations mode (t p.1) n p.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    change Measurable (fun p : Ω × (History n × ℝ) =>
      (causalInnovations mode (t p.1) n p.2.1,
        innovation (mode n) (t p.1 n p.2.1) p.2.2))
    have hp : Measurable (fun p : Ω × (History n × ℝ) => (p.1,p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hfirst : Measurable (fun p : Ω × (History n × ℝ) =>
        causalInnovations mode (t p.1) n p.2.1) := ih.comp hp
    have htarget : Measurable (fun p : Ω × (History n × ℝ) => t p.1 n p.2.1) :=
      (ht n).comp hp
    have hsecond : Measurable (fun p : Ω × (History n × ℝ) =>
        innovation (mode n) (t p.1 n p.2.1) p.2.2) :=
      (innovation_measurable (mode n)).comp
        (f := fun p : Ω × (History n × ℝ) => (t p.1 n p.2.1,p.2.2))
        (htarget.prodMk (measurable_snd.comp measurable_snd))
    exact hfirst.prodMk hsecond


theorem parameterized_causal_measurePreserving (μ : Measure Ω) [SFinite μ]
    (mode : ℕ → Option ℕ) (t : Ω → (n : ℕ) → History n → ℝ)
    (ht : ∀ n, Measurable (fun p : Ω × History n => t p.1 n p.2)) (n : ℕ) :
    MeasurePreserving (fun p : Ω × History n =>
      (p.1,causalInnovations mode (t p.1) n p.2))
      (μ.prod (historyNoise n)) (μ.prod (historyNoise n)) := by
  have hf (ω : Ω) (j : ℕ) : Measurable (t ω j) :=
    (ht j).comp (measurable_const.prodMk measurable_id)
  exact (MeasurePreserving.id μ).skew_product
    (causal_innovations_joint_measurable mode t ht n)
    (Filter.Eventually.of_forall fun ω =>
      (causal_innovations_measurePreserving mode (t ω) (hf ω) n).map_eq)

theorem parameterized_causal_joint_law (μ : Measure Ω) [SFinite μ]
    (mode : ℕ → Option ℕ) (t : Ω → (n : ℕ) → History n → ℝ)
    (ht : ∀ n, Measurable (fun p : Ω × History n => t p.1 n p.2)) (n : ℕ) :
    Measure.map (fun p : Ω × History n =>
      (p.1,causalInnovations mode (t p.1) n p.2))
      (μ.prod (historyNoise n)) = μ.prod (historyNoise n) :=
  (parameterized_causal_measurePreserving μ mode t ht n).map_eq


theorem actual_errors_joint_measurable (mode : ℕ → Option ℕ)
    (origin step weight : Ω → ℕ → ℝ) (U : Ω → ℕ → ℕ → ℝ)
    (ho : ∀ j, Measurable (fun ω => origin ω j))
    (hs : ∀ j, Measurable (fun ω => step ω j))
    (hw : ∀ j, Measurable (fun ω => weight ω j))
    (hU : ∀ i j, Measurable (fun ω => U ω i j)) (n : ℕ) :
    Measurable (fun p : Ω × History n => errors mode (origin p.1) (step p.1) (weight p.1) (U p.1) n p.2) := by
  induction n with
  | zero => apply measurable_pi_iff.mpr; intro i; exact Fin.elim0 i
  | succ n ih =>
    apply measurable_pi_iff.mpr
    intro i
    have hp : Measurable (fun p : Ω × (History n × ℝ) => (p.1,p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have he (j : Fin n) : Measurable (fun p : Ω × (History n × ℝ) =>
        errors mode (origin p.1) (step p.1) (weight p.1) (U p.1) n p.2.1 j) :=
      (measurable_pi_apply j).comp (ih.comp hp)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [errors, Fin.snoc_last]
      change Measurable (fun p : Ω × (History n × ℝ) => origin p.1 n + step p.1 n *
        reconstruct (mode n) ((weight p.1 n - ∑ j : Fin n,
          errors mode (origin p.1) (step p.1) (weight p.1) (U p.1) n p.2.1 j * U p.1 j.val n
          - origin p.1 n)/step p.1 n) p.2.2 - weight p.1 n)
      have ht : Measurable (fun p : Ω × (History n × ℝ) =>
          (weight p.1 n - ∑ j : Fin n,
            errors mode (origin p.1) (step p.1) (weight p.1) (U p.1) n p.2.1 j * U p.1 j.val n
            - origin p.1 n)/step p.1 n) := by
        apply Measurable.div
        · apply Measurable.sub
          · apply Measurable.sub
            · exact (hw n).comp measurable_fst
            · exact Finset.measurable_sum _ (fun j _ => (he j).mul ((hU j.val n).comp measurable_fst))
          · exact (ho n).comp measurable_fst
        · exact (hs n).comp measurable_fst
      exact (((ho n).comp measurable_fst).add (((hs n).comp measurable_fst).mul
        ((reconstruct_measurable (mode n)).comp
          (ht.prodMk (measurable_snd.comp measurable_snd))))).sub ((hw n).comp measurable_fst)
    · simp only [errors, Fin.snoc_castSucc]
      exact he j

theorem actual_target_joint_measurable (mode : ℕ → Option ℕ)
    (origin step weight : Ω → ℕ → ℝ) (U : Ω → ℕ → ℕ → ℝ)
    (ho : ∀ j, Measurable (fun ω => origin ω j))
    (hs : ∀ j, Measurable (fun ω => step ω j))
    (hw : ∀ j, Measurable (fun ω => weight ω j))
    (hU : ∀ i j, Measurable (fun ω => U ω i j)) (n : ℕ) :
    Measurable (fun p : Ω × History n => target mode (origin p.1) (step p.1) (weight p.1) (U p.1) n p.2) := by
  have he (j : Fin n) := (measurable_pi_apply j).comp
    (actual_errors_joint_measurable mode origin step weight U ho hs hw hU n)
  exact ((hw n).comp measurable_fst).sub
    (Finset.measurable_sum _ (fun j _ => (he j).mul ((hU j.val n).comp measurable_fst)))

theorem actual_normalizedTarget_joint_measurable (mode : ℕ → Option ℕ)
    (origin step weight : Ω → ℕ → ℝ) (U : Ω → ℕ → ℕ → ℝ)
    (ho : ∀ j, Measurable (fun ω => origin ω j))
    (hs : ∀ j, Measurable (fun ω => step ω j))
    (hw : ∀ j, Measurable (fun ω => weight ω j))
    (hU : ∀ i j, Measurable (fun ω => U ω i j)) (n : ℕ) :
    Measurable (fun p : Ω × History n =>
      normalizedTarget mode (origin p.1) (step p.1) (weight p.1) (U p.1) n p.2) :=
  ((actual_target_joint_measurable mode origin step weight U ho hs hw hU n).sub
    ((ho n).comp measurable_fst)).div ((hs n).comp measurable_fst)


theorem actual_upstream_measurePreserving_of_target (μ : Measure Ω) [SFinite μ]
    (mode : ℕ → Option ℕ) (origin step weight : Ω → ℕ → ℝ) (U : Ω → ℕ → ℕ → ℝ)
    (ht : ∀ n, Measurable (fun p : Ω × History n =>
      normalizedTarget mode (origin p.1) (step p.1) (weight p.1) (U p.1) n p.2)) (n : ℕ) :
    MeasurePreserving (fun p : Ω × History n =>
      (p.1,causalInnovations mode (normalizedTarget mode (origin p.1) (step p.1) (weight p.1) (U p.1)) n p.2))
      (μ.prod (historyNoise n)) (μ.prod (historyNoise n)) :=
  parameterized_causal_measurePreserving μ mode
    (fun ω => normalizedTarget mode (origin ω) (step ω) (weight ω) (U ω)) ht n


theorem actual_upstream_measurePreserving (μ : Measure Ω) [SFinite μ]
    (mode : ℕ → Option ℕ) (origin step weight : Ω → ℕ → ℝ) (U : Ω → ℕ → ℕ → ℝ)
    (ho : ∀ j, Measurable (fun ω => origin ω j))
    (hs : ∀ j, Measurable (fun ω => step ω j))
    (hw : ∀ j, Measurable (fun ω => weight ω j))
    (hU : ∀ i j, Measurable (fun ω => U ω i j)) (n : ℕ) :
    MeasurePreserving (fun p : Ω × History n =>
      (p.1,causalInnovations mode (normalizedTarget mode (origin p.1) (step p.1) (weight p.1) (U p.1)) n p.2))
      (μ.prod (historyNoise n)) (μ.prod (historyNoise n)) :=
  actual_upstream_measurePreserving_of_target μ mode origin step weight U
    (actual_normalizedTarget_joint_measurable mode origin step weight U ho hs hw hU) n

theorem actual_upstream_joint_law (μ : Measure Ω) [SFinite μ]
    (mode : ℕ → Option ℕ) (origin step weight : Ω → ℕ → ℝ) (U : Ω → ℕ → ℕ → ℝ)
    (ho : ∀ j, Measurable (fun ω => origin ω j))
    (hs : ∀ j, Measurable (fun ω => step ω j))
    (hw : ∀ j, Measurable (fun ω => weight ω j))
    (hU : ∀ i j, Measurable (fun ω => U ω i j)) (n : ℕ) :
    Measure.map (fun p : Ω × History n =>
      (p.1,causalInnovations mode (normalizedTarget mode (origin p.1) (step p.1) (weight p.1) (U p.1)) n p.2))
      (μ.prod (historyNoise n)) = μ.prod (historyNoise n) :=
  (actual_upstream_measurePreserving μ mode origin step weight U ho hs hw hU n).map_eq


theorem fresh_dependent_target_zero (u : ℝ) : innovation none (-u) u = 0 := by
  simp [innovation, reconstruct, recenter, grid]

theorem fresh_dependent_target_second :
    (∫ u, (innovation none (-u) u)^2 ∂noise) = 0 := by
  simp only [fresh_dependent_target_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp

end
end QepFeedbackUpstream
