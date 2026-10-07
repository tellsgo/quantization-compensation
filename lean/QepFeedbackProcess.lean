import QepFeedbackInnovation
set_option maxHeartbeats 1800000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation
namespace QepFeedbackProcess
noncomputable section


def errors (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) : (n : ℕ) → History n → Fin n → ℝ
  | 0 => fun _ i => Fin.elim0 i
  | n+1 => fun p =>
    let e := errors mode origin step weight U n p.1
    let z := weight n - ∑ i : Fin n, e i * U i.val n
    Fin.snoc e (origin n + step n * reconstruct (mode n) ((z-origin n)/step n) p.2 - weight n)

def target (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) : ℝ :=
  weight n - ∑ i : Fin n, errors mode origin step weight U n p i * U i.val n

def normalizedTarget (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) : ℝ :=
  (target mode origin step weight U n p-origin n)/step n

def quantized (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History (n+1)) : ℝ :=
  origin n + step n * reconstruct (mode n) (normalizedTarget mode origin step weight U n p.1) p.2

def freshInnovation (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History (n+1)) : ℝ :=
  step n * innovation (mode n) (normalizedTarget mode origin step weight U n p.1) p.2

def overload (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History n) : ℝ :=
  origin n + step n * recenter (mode n) (normalizedTarget mode origin step weight U n p) - target mode origin step weight U n p

theorem reconstruct_measurable (mode : Option ℕ) :
    Measurable (fun p : ℝ × ℝ => reconstruct mode p.1 p.2) := by
  cases mode with
  | none => exact (grid_measurable.comp (measurable_fst.add measurable_snd)).sub measurable_snd
  | some k =>
    unfold reconstruct reconstruction quant clip
    exact (measurable_const.max (measurable_const.min
      (grid_measurable.comp (measurable_fst.add measurable_snd)))).sub measurable_snd

theorem errors_measurable (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) : Measurable (errors mode origin step weight U n) := by
  induction n with
  | zero => apply measurable_pi_iff.mpr; intro i; exact Fin.elim0 i
  | succ n ih =>
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [errors, Fin.snoc_last]
      change Measurable (fun p : History n × ℝ => origin n + step n * reconstruct (mode n)
        ((weight n - ∑ j : Fin n, errors mode origin step weight U n p.1 j * U j.val n-origin n)/step n) p.2 - weight n)
      have he (j : Fin n) : Measurable (fun p : History n × ℝ => errors mode origin step weight U n p.1 j) :=
        (measurable_pi_apply j).comp (ih.comp measurable_fst)
      have ht : Measurable (fun p : History n × ℝ =>
          (weight n - ∑ j : Fin n, errors mode origin step weight U n p.1 j * U j.val n-origin n)/step n) := by
        fun_prop
      exact (measurable_const.add (measurable_const.mul
        ((reconstruct_measurable (mode n)).comp (ht.prodMk measurable_snd)))).sub measurable_const
    · simp only [errors,Fin.snoc_castSucc]
      exact ((measurable_pi_apply j).comp ih).comp measurable_fst

theorem target_measurable (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) : Measurable (target mode origin step weight U n) := by
  have he (j : Fin n) := (measurable_pi_apply j).comp (errors_measurable mode origin step weight U n)
  unfold target
  fun_prop

theorem normalizedTarget_measurable (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) : Measurable (normalizedTarget mode origin step weight U n) :=
  ((target_measurable mode origin step weight U n).sub measurable_const).div_const _


theorem actual_complete_history_law (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) :
    Measure.map (fun p : History (n+1) => (p.1,
      innovation (mode n) (normalizedTarget mode origin step weight U n p.1) p.2))
      (historyNoise (n+1)) = historyNoise (n+1) :=
  (complete_history_law (historyNoise n) (mode n) (normalizedTarget mode origin step weight U n)
    (normalizedTarget_measurable mode origin step weight U n)).map_eq


theorem actual_innovations_joint_law (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) :
    Measure.map (causalInnovations mode (normalizedTarget mode origin step weight U) n)
      (historyNoise n) = historyNoise n :=
  causal_innovations_joint_law mode _ (normalizedTarget_measurable mode origin step weight U) n

theorem last_error (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History (n+1)) :
    errors mode origin step weight U (n+1) p (Fin.last n) = quantized mode origin step weight U n p-weight n := by
  simp only [errors,Fin.snoc_last,quantized,normalizedTarget,target]

theorem actual_column_identity (mode : ℕ → Option ℕ) (origin step weight : ℕ → ℝ)
    (U : ℕ → ℕ → ℝ) (n : ℕ) (p : History (n+1)) :
    errors mode origin step weight U (n+1) p (Fin.last n) +
      (∑ i : Fin n, errors mode origin step weight U n p.1 i * U i.val n) =
      freshInnovation mode origin step weight U n p + overload mode origin step weight U n p.1 := by
  rw [last_error]
  unfold freshInnovation overload quantized innovation normalizedTarget target
  ring

theorem unbounded_overload_zero (origin step weight : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (hstep : ∀ n, step n ≠ 0) (n : ℕ) (p : History n) :
    overload (fun _ => none) origin step weight U n p = 0 := by
  unfold overload recenter normalizedTarget
  field_simp [hstep n]
  <;> ring

end
end QepFeedbackProcess
