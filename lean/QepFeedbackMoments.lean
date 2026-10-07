import QepFeedbackInnovation
set_option maxHeartbeats 1800000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepFeedbackInnovation
namespace QepFeedbackMoments
noncomputable section


def linear (a : ℕ → ℝ) : (n : ℕ) → History n → ℝ
  | 0 => fun _ => 0
  | n+1 => fun p => linear a n p.1 + a n * p.2

theorem linear_measurable (a : ℕ → ℝ) (n : ℕ) : Measurable (linear a n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).add (measurable_const.mul measurable_snd)

theorem id_integrable : Integrable (fun u : ℝ => u) noise := by
  simpa only [pow_one] using noise_integrable_power 1

theorem add_fresh_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ) :
    Integrable (fun p : Ω × ℝ => f p.1 + c*p.2) (μ.prod noise) :=
  (hf.comp_fst noise).add ((id_integrable.const_mul c).comp_snd μ)

theorem add_fresh_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) (c : ℝ) :
    Integrable (fun p : Ω × ℝ => (f p.1 + c*p.2)^2) (μ.prod noise) := by
  have hx := hf.mul_prod id_integrable
  have h := ((hf2.comp_fst noise).add (hx.const_mul (2*c))).add
    (((noise_integrable_power 2).const_mul (c^2)).comp_snd μ)
  convert h using 1
  funext p; dsimp only [Pi.add_apply]; ring

theorem add_fresh_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ) :
    (∫ p : Ω × ℝ, f p.1+c*p.2 ∂μ.prod noise) = ∫ x, f x ∂μ := by
  rw [integral_add (hf.comp_fst noise) ((id_integrable.const_mul c).comp_snd μ),
    integral_fun_fst,integral_fun_snd,integral_const_mul,noise_mean]
  simp

theorem add_fresh_second {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) (c : ℝ) :
    (∫ p : Ω × ℝ, (f p.1+c*p.2)^2 ∂μ.prod noise) = (∫ x, (f x)^2 ∂μ)+c^2/12 := by
  have hx := hf.mul_prod id_integrable
  have heq : (fun p : Ω × ℝ => (f p.1+c*p.2)^2) =
      (fun p : Ω × ℝ => (f p.1)^2+(2*c)*(f p.1*p.2)+c^2*p.2^2) := by funext p; ring
  have ha : Integrable (fun p : Ω × ℝ => (f p.1)^2+(2*c)*(f p.1*p.2)) (μ.prod noise) :=
    (hf2.comp_fst noise).add (hx.const_mul (2*c))
  rw [heq,integral_add ha
    (((noise_integrable_power 2).const_mul (c^2)).comp_snd μ),
    integral_add (hf2.comp_fst noise) (hx.const_mul (2*c)),integral_const_mul,
    integral_fun_fst (fun x => (f x)^2),integral_fun_snd (fun u : ℝ => c^2*u^2),
    integral_const_mul,integral_prod_mul f (fun u : ℝ => u),noise_mean,noise_second_moment]
  simp; ring

theorem linear_integrable (a : ℕ → ℝ) (n : ℕ) : Integrable (linear a n) (historyNoise n) := by
  induction n with
  | zero => exact integrable_const (0:ℝ)
  | succ n ih => exact add_fresh_integrable (historyNoise n) (linear a n) ih (a n)

theorem linear_square_integrable (a : ℕ → ℝ) (n : ℕ) :
    Integrable (fun p => (linear a n p)^2) (historyNoise n) := by
  induction n with
  | zero => simpa only [linear,zero_pow (by decide : 2≠0)] using (integrable_const (0:ℝ) : Integrable (fun _ : History 0 => (0:ℝ)) (historyNoise 0))
  | succ n ih => exact add_fresh_square_integrable (historyNoise n) (linear a n) (linear_integrable a n) ih (a n)

theorem linear_mean (a : ℕ → ℝ) (n : ℕ) : (∫ p, linear a n p ∂historyNoise n)=0 := by
  induction n with
  | zero => simp [linear]
  | succ n ih => exact (add_fresh_mean (historyNoise n) (linear a n) (linear_integrable a n) (a n)).trans ih

theorem linear_second (a : ℕ → ℝ) (n : ℕ) :
    (∫ p, (linear a n p)^2 ∂historyNoise n) = ∑ i : Fin n, (a i.val)^2/12 := by
  induction n with
  | zero => simp [linear]
  | succ n ih =>
    change (∫ p : History n × ℝ, (linear a n p.1+a n*p.2)^2 ∂(historyNoise n).prod noise) = _
    rw [add_fresh_second _ _ (linear_integrable a n) (linear_square_integrable a n),ih,Fin.sum_univ_castSucc]
    rfl


theorem actual_linear_mean (mode : ℕ → Option ℕ) (target : (n : ℕ) → History n → ℝ)
    (ht : ∀ n,Measurable (target n)) (a : ℕ → ℝ) (n : ℕ) :
    (∫ p, linear a n (causalInnovations mode target n p) ∂historyNoise n)=0 := by
  have mp := causal_innovations_measurePreserving mode target ht n
  have h := integral_map_of_stronglyMeasurable (μ:=historyNoise n) mp.measurable (linear_measurable a n).stronglyMeasurable
  rw [mp.map_eq] at h
  exact h.symm.trans (linear_mean a n)

theorem actual_linear_second (mode : ℕ → Option ℕ) (target : (n : ℕ) → History n → ℝ)
    (ht : ∀ n,Measurable (target n)) (a : ℕ → ℝ) (n : ℕ) :
    (∫ p, (linear a n (causalInnovations mode target n p))^2 ∂historyNoise n)=
      ∑ i : Fin n, (a i.val)^2/12 := by
  have mp := causal_innovations_measurePreserving mode target ht n
  have h := integral_map_of_stronglyMeasurable (μ:=historyNoise n) mp.measurable
    ((linear_measurable a n).pow_const 2).stronglyMeasurable
  rw [mp.map_eq] at h
  exact h.symm.trans (linear_second a n)

def coordinates : (n : ℕ) → History n → Fin n → ℝ
  | 0 => fun _ i => Fin.elim0 i
  | n+1 => fun p => Fin.snoc (coordinates n p.1) p.2

theorem linear_sum (a : ℕ → ℝ) (n : ℕ) (p : History n) :
    linear a n p = ∑ i : Fin n, a i.val * coordinates n p i := by
  induction n with
  | zero => simp [linear]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [linear,coordinates,Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last]
    rw [ih]


end
end QepFeedbackMoments
