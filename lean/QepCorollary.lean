import QepCorrected




set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QepCorollary
noncomputable section
open QepCorrected
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def loss (A B : Mat ι κ) (P : Mat κ κ) (a : ℝ) : ℝ :=
  fSq (residual A B (A * P) a)

def nonincreasing (A B : Mat ι κ) (P : Mat κ κ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → loss A B P b ≤ loss A B P a

theorem zero_direction_of_zero_energy (S : Mat ι κ) (h : fSq S = 0) : S = 0 := by
  classical
  ext i j
  have hj : (S i j)^2 ≤ ∑ k, (S i k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (S i k)) (Finset.mem_univ j)
  have hi : (∑ k, (S i k)^2) ≤ fSq S := by
    unfold fSq
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (S k l)) (Finset.mem_univ i)
  change S i j = 0
  nlinarith [sq_nonneg (S i j)]

theorem cross_zero_of_energy_zero (A B : Mat ι κ) (P : Mat κ κ)
    (hd : fSq (A * P) = 0) : fInner B (A * P) = 0 := by
  rw [zero_direction_of_zero_energy (A * P) hd]
  simp [fInner]

theorem nonincreasing_iff_cross_nonpos (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) :
    nonincreasing A B P ↔ fInner B (A * P) ≤ 0 := by
  let d := fSq (A * P)
  let c := fInner B (A * P)
  have hd : 0 ≤ d := fSq_nonneg _
  constructor
  · intro h
    by_contra hn
    have hc : 0 < c := lt_of_not_ge hn
    let t := c / (d + c)
    have hden : 0 < d + c := by linarith
    have ht : 0 < t := div_pos hc hden
    have htu : t ≤ 1 := (div_le_one hden).mpr (by linarith)
    have he : t * (d + c) = c := div_mul_cancel₀ c (ne_of_gt hden)
    have htd : t * d ≤ c := by nlinarith
    have hpos : 0 < t * (2*c-t*d) := mul_pos ht (by linarith)
    have hmono := h (1-t) 1 (by linarith) (by linarith) (by norm_num)
    have hg := pair_gap A B P hs hp (1-t) 1
    change loss A B P 1 - loss A B P (1-t) =
      (1-(1-t))*(((1-t)+1-2)*d+2*c) at hg
    have hid : (1-(1-t))*(((1-t)+1-2)*d+2*c) = t*(2*c-t*d) := by ring
    rw [hid] at hg
    linarith
  · intro hc a b ha hab hb
    have hcoef : (a+b-2)*d+2*c ≤ 0 := by
      have ht : a+b-2 ≤ 0 := by linarith
      have hm := mul_nonpos_of_nonpos_of_nonneg ht hd
      change c ≤ 0 at hc
      linarith
    have hg := pair_gap A B P hs hp a b
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) hcoef
    change loss A B P b - loss A B P a = (b-a)*((a+b-2)*d+2*c) at hg
    linarith

theorem nonincreasing_iff (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) :
    nonincreasing A B P ↔ fInner B (A * P) ≤ 0 ∨ fSq (A * P) = 0 := by
  rw [nonincreasing_iff_cross_nonpos A B P hs hp]
  constructor
  · exact Or.inl
  · intro h
    rcases h with h|h
    · exact h
    · rw [cross_zero_of_energy_zero A B P h]

theorem all_strengths_improve_iff (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) :
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 → loss A B P a ≤ loss A B P 0) ↔
      2 * fInner B (A * P) ≤ fSq (A * P) := by
  constructor
  · intro h
    have hh := (improvement_iff A B P hs hp 1 (by norm_num)).mp
      (h 1 (by norm_num) (by norm_num))
    norm_num at hh
    exact hh
  · intro h a ha hu
    rcases eq_or_lt_of_le ha with he|he
    · subst a
      exact le_rfl
    · apply (improvement_iff A B P hs hp a he).mpr
      have hd := fSq_nonneg (A * P)
      have hm := mul_nonneg (show 0 ≤ 1-a by linarith) hd
      nlinarith

def clipped (d c : ℝ) : ℝ := max 0 (min 1 (1-c/d))

theorem clipped_mem (d c : ℝ) : 0 ≤ clipped d c ∧ clipped d c ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem scalar_clipped_gap_nonpos (d c a : ℝ) (hd : 0 < d)
    (ha : 0 ≤ a) (hu : a ≤ 1) :
    (clipped d c-a)*((a+clipped d c-2)*d+2*c) ≤ 0 := by
  by_cases hc : c ≤ 0
  · have hv : 1 ≤ 1-c/d := by
      have ht := div_nonpos_of_nonpos_of_nonneg hc (le_of_lt hd)
      linarith
    have hs : clipped d c = 1 := by simp [clipped, min_eq_left hv]
    rw [hs]
    apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
    have hm := mul_nonpos_of_nonpos_of_nonneg (show a+1-2 ≤ 0 by linarith) (le_of_lt hd)
    linarith
  · by_cases hc2 : d ≤ c
    · have hv : 1-c/d ≤ 0 := by
        have ht : 1 ≤ c/d := (le_div_iff₀ hd).mpr (by simpa using hc2)
        linarith
      have hs : clipped d c = 0 := by
        unfold clipped
        exact max_eq_left (le_trans (min_le_right _ _) hv)
      rw [hs]
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
      have hm := mul_nonneg ha (le_of_lt hd)
      nlinarith
    · have hcpos : 0 < c := lt_of_not_ge hc
      have hclt : c < d := lt_of_not_ge hc2
      let v := 1-c/d
      have hv0 : 0 ≤ v := by
        have ht : c/d ≤ 1 := (div_le_one hd).mpr (le_of_lt hclt)
        dsimp [v]
        linarith
      have hv1 : v ≤ 1 := by
        have ht := div_nonneg (le_of_lt hcpos) (le_of_lt hd)
        dsimp [v]
        linarith
      have hs : clipped d c = v := by
        unfold clipped
        rw [min_eq_right hv1, max_eq_right hv0]
      have he : c = (1-v)*d := by
        dsimp [v]
        field_simp
        <;> ring
      rw [hs]
      have hid : (v-a)*((a+v-2)*d+2*c) = -d*(a-v)^2 := by rw [he]; ring
      rw [hid]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

theorem optimal_strength_minimizes (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) (hd : 0 < fSq (A * P)) :
    let s := clipped (fSq (A * P)) (fInner B (A * P))
    (0 ≤ s ∧ s ≤ 1) ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → loss A B P s ≤ loss A B P a := by
  dsimp
  refine ⟨clipped_mem _ _, ?_⟩
  intro a ha hu
  have hg := pair_gap A B P hs hp a (clipped (fSq (A*P)) (fInner B (A*P)))
  have hn := scalar_clipped_gap_nonpos (fSq (A*P)) (fInner B (A*P)) a hd ha hu
  change loss A B P _ - loss A B P a = _ at hg
  linarith

def frobeniusResidual (A B : Mat ι κ) (P : Mat κ κ) (a : ℝ) : ℝ :=
  Real.sqrt (loss A B P a)

theorem frobenius_order_iff (A B : Mat ι κ) (P : Mat κ κ) (a b : ℝ) :
    frobeniusResidual A B P a ≤ frobeniusResidual A B P b ↔
      loss A B P a ≤ loss A B P b :=
  Real.sqrt_le_sqrt_iff (fSq_nonneg _)

theorem frobenius_nonincreasing_iff (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) :
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      frobeniusResidual A B P b ≤ frobeniusResidual A B P a) ↔
      fInner B (A * P) ≤ 0 ∨ fSq (A * P) = 0 := by
  simp_rw [frobenius_order_iff]
  exact nonincreasing_iff A B P hs hp

theorem frobenius_all_strengths_improve_iff (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) :
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      frobeniusResidual A B P a ≤ frobeniusResidual A B P 0) ↔
      2 * fInner B (A * P) ≤ fSq (A * P) := by
  simp_rw [frobenius_order_iff]
  exact all_strengths_improve_iff A B P hs hp

theorem frobenius_optimal_strength_minimizes (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) (hd : 0 < fSq (A * P)) :
    let s := clipped (fSq (A * P)) (fInner B (A * P))
    (0 ≤ s ∧ s ≤ 1) ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      frobeniusResidual A B P s ≤ frobeniusResidual A B P a := by
  dsimp
  simp_rw [frobenius_order_iff]
  exact optimal_strength_minimizes A B P hs hp hd

end
end QepCorollary
