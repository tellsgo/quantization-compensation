import QepFeedbackProcess
import QepFeedbackMoments
set_option maxHeartbeats 2200000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation QepFeedbackProcess QepFeedbackMoments
namespace QepFeedbackFiniteL2
noncomputable section


theorem quant_mem_interval (k : ℕ) (x : ℝ) : quant k x ∈ Icc (0:ℝ) k := by
  constructor
  · exact le_max_left _ _
  · exact max_le (Nat.cast_nonneg _) (min_le_left _ _)

theorem finite_reconstruction_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ) (t : Ω → ℝ) (ht : Measurable t)
    (a delta w : ℝ) :
    MemLp (fun p : Ω × ℝ => a+delta*reconstruction k (t p.1) p.2-w) 2 (μ.prod noise) := by
  have hq : Measurable (fun p : Ω × ℝ => quant k (t p.1+p.2)) := by
    unfold quant clip
    exact measurable_const.max (measurable_const.min (grid_measurable.comp ((ht.comp measurable_fst).add measurable_snd)))
  have hq2 : MemLp (fun p : Ω × ℝ => quant k (t p.1+p.2)) 2 (μ.prod noise) :=
    memLp_of_bounded (μ:=μ.prod noise) (a:=0) (b:=(k:ℝ))
      (Filter.Eventually.of_forall fun p : Ω × ℝ => quant_mem_interval k (t p.1+p.2)) hq.aestronglyMeasurable 2
  have hu : MemLp (fun u : ℝ => u) 2 noise :=
    (memLp_two_iff_integrable_sq (μ:=noise) (f:=fun u : ℝ => u) measurable_id.aestronglyMeasurable).mpr (noise_integrable_power 2)
  have hp : MemLp (fun p : Ω × ℝ => p.2) 2 (μ.prod noise) :=
    hu.comp_measurePreserving (measurePreserving_snd (μ:=μ) (ν:=noise))
  have hd : MemLp (fun p : Ω × ℝ => quant k (t p.1+p.2)-p.2) 2 (μ.prod noise) := hq2.sub hp
  have hs : MemLp (fun p : Ω × ℝ => delta*(quant k (t p.1+p.2)-p.2)) 2 (μ.prod noise) := hd.const_mul delta
  have ha : MemLp (fun p : Ω × ℝ => a+delta*(quant k (t p.1+p.2)-p.2)) 2 (μ.prod noise) := (memLp_const a).add hs
  change MemLp (fun p : Ω × ℝ => a+delta*(quant k (t p.1+p.2)-p.2)-w) 2 (μ.prod noise)
  exact ha.sub (memLp_const w)


theorem finite_errors_memLp (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (j : Fin n) :
    MemLp (fun p => errors (fun i => some (codes i)) origin step weight U n p j) 2 (historyNoise n) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [errors,Fin.snoc_last,reconstruct]
      exact finite_reconstruction_memLp (historyNoise n) (codes n)
          (normalizedTarget (fun i => some (codes i)) origin step weight U n)
          (normalizedTarget_measurable _ _ _ _ _ _) (origin n) (step n) (weight n)
    · simp only [errors,Fin.snoc_castSucc]
      exact (ih i).comp_measurePreserving (measurePreserving_fst (μ:=historyNoise n) (ν:=noise))

theorem finite_target_memLp (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) :
    MemLp (target (fun i => some (codes i)) origin step weight U n) 2 (historyNoise n) := by
  unfold target
  apply (memLp_const (weight n)).sub
  apply memLp_finsetSum
  intro i _
  exact (finite_errors_memLp codes origin step weight U n i).mul_const (U i.val n)

theorem finite_overload_memLp (codes : ℕ → ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) :
    MemLp (overload (fun i => some (codes i)) origin step weight U n) 2 (historyNoise n) := by
  have hm : Measurable (fun p => clip (codes n) (normalizedTarget (fun i => some (codes i)) origin step weight U n p)) :=
    measurable_const.max (measurable_const.min (normalizedTarget_measurable _ _ _ _ _ _))
  have hc : MemLp (fun p => clip (codes n) (normalizedTarget (fun i => some (codes i)) origin step weight U n p)) 2 (historyNoise n) := by
    apply memLp_of_bounded (a:=0) (b:=(codes n:ℝ)) _ hm.aestronglyMeasurable 2
    exact Filter.Eventually.of_forall fun p => ⟨le_max_left _ _,max_le (Nat.cast_nonneg _) (min_le_left _ _)⟩
  exact ((memLp_const (origin n)).add (hc.const_mul (step n))).sub (finite_target_memLp codes origin step weight U n)

end
end QepFeedbackFiniteL2
