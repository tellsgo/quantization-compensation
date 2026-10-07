import Mathlib








set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace QepCorrected
noncomputable section
open scoped BigOperators
variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [Fintype Ω]

abbrev Mat (ι κ : Type*) := Matrix ι κ ℝ

def fSq (A : Mat ι κ) : ℝ := ∑ i, ∑ j, (A i j)^2
def fInner (A B : Mat ι κ) : ℝ := ∑ i, ∑ j, A i j * B i j
def residual (A B S : Mat ι κ) (a : ℝ) : Mat ι κ :=
  fun i j => A i j - B i j - a * S i j

theorem inner_self (A : Mat ι κ) : fInner A A = fSq A := by
  simp only [fInner, fSq, pow_two]

theorem fSq_nonneg (A : Mat ι κ) : 0 ≤ fSq A := by
  unfold fSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _


theorem inner_right_mul (A B : Mat ι κ) (P : Mat κ κ) :
    fInner A (B * P) = fInner (A * P.transpose) B := by
  classical
  unfold fInner
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring


theorem projection_inner (A : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) :
    fInner A (A * P) = fSq (A * P) := by
  have h := inner_right_mul A (A * P) P
  rw [Matrix.mul_assoc, hp, hs] at h
  exact h.trans (inner_self (A * P))


theorem general_gap (A B S : Mat ι κ) (a : ℝ) :
    fSq (residual A B S a) - fSq (residual A B S 0) =
      a^2 * fSq S - 2*a*(fInner A S - fInner B S) := by
  have h : (∑ i, ∑ j,
      ((A i j-B i j-a*S i j)^2-(A i j-B i j)^2)) =
      ∑ i, ∑ j, (a^2*(S i j)^2-2*a*(A i j*S i j-B i j*S i j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [fSq, fInner, residual, zero_mul, sub_zero,
    Finset.sum_sub_distrib, ← Finset.mul_sum] using h


theorem projected_gap (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) (a : ℝ) :
    fSq (residual A B (A * P) a) - fSq (residual A B (A * P) 0) =
      -a*(2-a)*fSq (A * P) + 2*a*fInner B (A * P) := by
  rw [general_gap, projection_inner A P hs hp]
  ring


theorem improvement_iff (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) (a : ℝ) (ha : 0 < a) :
    fSq (residual A B (A * P) a) ≤ fSq (residual A B (A * P) 0) ↔
      2*fInner B (A * P) ≤ (2-a)*fSq (A * P) := by
  have hg := projected_gap A B P hs hp a
  have hf : fSq (residual A B (A * P) a) - fSq (residual A B (A * P) 0) =
      a*(2*fInner B (A * P)-(2-a)*fSq (A * P)) := by
    rw [hg]; ring
  constructor
  · intro h
    by_contra hn
    have hpos : 0 < 2*fInner B (A * P)-(2-a)*fSq (A * P) := by linarith
    have hm := mul_pos ha hpos
    linarith
  · intro h
    have hn : 2*fInner B (A * P)-(2-a)*fSq (A * P) ≤ 0 := by linarith
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hn
    linarith


theorem pair_gap (A B : Mat ι κ) (P : Mat κ κ)
    (hs : P.transpose = P) (hp : P * P = P) (a b : ℝ) :
    fSq (residual A B (A * P) b) - fSq (residual A B (A * P) a) =
      (b-a)*((a+b-2)*fSq (A*P)+2*fInner B (A*P)) := by
  have ha := projected_gap A B P hs hp a
  have hb := projected_gap A B P hs hp b
  calc
    _ = (-b*(2-b)*fSq (A*P)+2*b*fInner B (A*P)) -
        (-a*(2-a)*fSq (A*P)+2*a*fInner B (A*P)) := by linarith
    _ = _ := by ring


theorem finite_mean_gap (p : Ω → ℝ) (A B : Ω → Mat ι κ) (P : Ω → Mat κ κ)
    (hs : ∀ o, (P o).transpose = P o) (hp : ∀ o, P o * P o = P o) (a : ℝ) :
    (∑ o, p o * fSq (residual (A o) (B o) (A o * P o) a)) -
      (∑ o, p o * fSq (residual (A o) (B o) (A o * P o) 0)) =
      -a*(2-a)*(∑ o, p o*fSq (A o*P o)) +
        2*a*(∑ o, p o*fInner (B o) (A o*P o)) := by
  calc
    _ = ∑ o, p o * (fSq (residual (A o) (B o) (A o*P o) a) -
          fSq (residual (A o) (B o) (A o*P o) 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = ∑ o, (-a*(2-a)*(p o*fSq (A o*P o)) +
          2*a*(p o*fInner (B o) (A o*P o))) := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [projected_gap (A o) (B o) (P o) (hs o) (hp o) a]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]


theorem finite_mean_square_repair (p : Ω → ℝ) (A B : Ω → Mat ι κ)
    (P : Ω → Mat κ κ) (hs : ∀ o, (P o).transpose = P o)
    (hp : ∀ o, P o * P o = P o) (hpos : ∀ o, 0 ≤ p o)
    (hcross : (∑ o, p o*fInner (B o) (A o*P o)) = 0)
    (a : ℝ) (ha : 0 ≤ a) (hu : a ≤ 2) :
    (∑ o, p o*fSq (residual (A o) (B o) (A o*P o) a)) ≤
      (∑ o, p o*fSq (residual (A o) (B o) (A o*P o) 0)) := by
  have h := finite_mean_gap p A B P hs hp a
  rw [hcross, mul_zero, add_zero] at h
  have hd : 0 ≤ ∑ o, p o*fSq (A o*P o) := by
    exact Finset.sum_nonneg fun o _ => mul_nonneg (hpos o) (fSq_nonneg _)
  have hprod : 0 ≤ a*(2-a)*(∑ o, p o*fSq (A o*P o)) :=
    mul_nonneg (mul_nonneg ha (by linarith)) hd
  nlinarith

end
end QepCorrected
