import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace QepV1
noncomputable section
open scoped BigOperators


def weightedBound (a c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => a n * weightedBound a c n + c n

theorem weightedBound_closed (a c : ℕ → ℝ) (n : ℕ) :
    weightedBound a c n =
      ∑ k ∈ Finset.Ico 0 n, c k * ∏ j ∈ Finset.Ico (k+1) n, a j := by
  induction n with
  | zero => simp [weightedBound]
  | succ n ih =>
    rw [weightedBound, ih, Finset.sum_Ico_succ_top (Nat.zero_le n),
      Finset.Ico_self, Finset.prod_empty, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_Ico_succ_top (by have := Finset.mem_Ico.mp hk; omega)]
    ring

theorem recurrence_bound (u a c : ℕ → ℝ) (L : ℕ) (h0 : u 0 ≤ 0)
    (ha : ∀ k < L, 0 ≤ a k)
    (hstep : ∀ k < L, u (k+1) ≤ a k * u k + c k) :
    u L ≤ weightedBound a c L := by
  have h : ∀ n ≤ L, u n ≤ weightedBound a c n := by
    intro n hn
    induction n with
    | zero => exact h0
    | succ n ih =>
      have hi := ih (by omega)
      calc
        u (n+1) ≤ a n * u n + c n := hstep n (by omega)
        _ ≤ a n * weightedBound a c n + c n := by gcongr; exact ha n (by omega)
        _ = weightedBound a c (n+1) := rfl
  exact h L le_rfl

theorem weightedBound_nonneg (a c : ℕ → ℝ) (L : ℕ)
    (ha : ∀ k < L, 0 ≤ a k) (hc : ∀ k < L, 0 ≤ c k) :
    0 ≤ weightedBound a c L := by
  rw [weightedBound_closed]
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg (hc k (Finset.mem_Ico.mp hk).2)
  apply Finset.prod_nonneg
  intro j hj
  exact ha j (Finset.mem_Ico.mp hj).2


def scalarTarget (w x z a : ℝ) : ℝ := w + a * w * (x-z) * z / (z*z)

theorem scalar_target_times_input (w x z a : ℝ) (hz : z ≠ 0) :
    scalarTarget w x z a * z = w*z + a*w*(x-z) := by
  unfold scalarTarget
  field_simp


theorem scalar_preactivation_difference (w e x q b a : ℝ) (hq : q ≠ 0) :
    (scalarTarget w x q a+e)*q - (w+e)*b =
      (1-a)*w*(q-b) + e*(q-b) + a*w*(x-b) := by
  rw [add_mul, scalar_target_times_input w x q a hq]
  ring

theorem scalar_layer_distance (w e x q b a γ : ℝ) (σ : ℝ → ℝ)
    (hq : q ≠ 0) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hγ : 0 ≤ γ)
    (hσ : ∀ u v, |σ u-σ v| ≤ γ* |u-v|) :
    |σ ((scalarTarget w x q a+e)*q)-σ ((w+e)*b)| ≤
      γ*(|w|+|e|)* |q-b| + a*γ* |w| * |x-b| := by
  have h := hσ ((scalarTarget w x q a+e)*q) ((w+e)*b)
  rw [scalar_preactivation_difference w e x q b a hq] at h
  have ht := abs_add_le ((1-a)*w*(q-b)+e*(q-b)) (a*w*(x-b))
  have hs := abs_add_le ((1-a)*w*(q-b)) (e*(q-b))
  have hab : |(1-a)*w*(q-b)+e*(q-b)+a*w*(x-b)| ≤
      (1-a)* |w| * |q-b|+|e| * |q-b|+a* |w| * |x-b| := by
    simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr ha1), abs_of_nonneg ha0] at ht hs
    linarith
  have hm := mul_le_mul_of_nonneg_left hab hγ
  have hn : 0 ≤ a*γ* |w| * |q-b| := by positivity
  nlinarith



theorem scalar_trajectory_recurrence
    (w e a γ X B Q : ℕ → ℝ) (σ : ℕ → ℝ → ℝ) (L : ℕ)
    (hQ : ∀ k < L, Q (k+1)=σ k ((scalarTarget (w k) (X k) (Q k) (a k)+e k)*Q k))
    (hB : ∀ k < L, B (k+1)=σ k ((w k+e k)*B k))
    (hlegal : ∀ k < L, Q k ≠ 0)
    (hα : ∀ k < L, 0 ≤ a k ∧ a k ≤ 1)
    (hγ : ∀ k < L, 0 ≤ γ k)
    (hlip : ∀ k < L, ∀ u v, |σ k u-σ k v| ≤ γ k* |u-v|) :
    ∀ k < L, |Q (k+1)-B (k+1)| ≤
      γ k*(|w k|+|e k|)* |Q k-B k| + a k*γ k* |w k| * |X k-B k| := by
  intro k hk
  rw [hQ k hk, hB k hk]
  exact scalar_layer_distance _ _ _ _ _ _ _ _ (hlegal k hk)
    (hα k hk).1 (hα k hk).2 (hγ k hk) (hlip k hk)




theorem cross_terminal_loose (D db dq a b r : ℕ → ℝ) (L : ℕ)
    (hD0 : D 0 = 0) (hb0 : db 0 = 0)
    (hbnonneg : ∀ k < L, 0 ≤ db k)
    (ha : ∀ k < L, 0 ≤ a k) (hba : ∀ k < L, b k ≤ a k)
    (hD : ∀ k < L, D (k+1) ≤ a k*D k+b k*db k)
    (hbase : ∀ k < L, db (k+1) ≤ r k)
    (htriangle : dq L ≤ db L+D L) :
    dq L ≤ weightedBound a r L := by
  apply htriangle.trans
  apply recurrence_bound (fun k => db k+D k) a r L
  · simp [hD0,hb0]
  · exact ha
  · intro k hk
    have h1 := hD k hk
    have h2 := hbase k hk
    have h3 := mul_le_mul_of_nonneg_right (hba k hk) (hbnonneg k hk)
    nlinarith



theorem cross_terminal_tight (D db dq a b r : ℕ → ℝ) (L : ℕ)
    (hD1 : D 1 ≤ 0)
    (ha : ∀ k < L+1, 0 ≤ a k) (hb : ∀ k < L+1, 0 ≤ b k)
    (hD : ∀ k < L+1, D (k+1) ≤ a k*D k+b k*db k)
    (hbase : ∀ k < L+1, db (k+1) ≤ r k)
    (htriangle : dq (L+1) ≤ db (L+1)+D (L+1)) :
    dq (L+1) ≤ r L +
      weightedBound (fun k => a (k+1)) (fun k => b (k+1)*r k) L := by
  have hrec : D (L+1) ≤
      weightedBound (fun k => a (k+1)) (fun k => b (k+1)*r k) L := by
    apply recurrence_bound (fun k => D (k+1)) _ _ L hD1
    · intro k hk; exact ha (k+1) (by omega)
    · intro k hk
      have h1 := hD (k+1) (by omega)
      have h2 := mul_le_mul_of_nonneg_left (hbase k (by omega)) (hb (k+1) (by omega))
      exact h1.trans (by linarith)
  have hlast := hbase L (by omega)
  linarith



theorem scalar_actual_composite
    (w e a γ X B Q : ℕ → ℝ) (σ : ℕ → ℝ → ℝ) (L : ℕ)
    (hinitB : B 0=X 0) (hinitQ : Q 0=X 0)
    (hX : ∀ k < L, X (k+1)=σ k (w k*X k))
    (hQ : ∀ k < L, Q (k+1)=σ k ((scalarTarget (w k) (X k) (Q k) (a k)+e k)*Q k))
    (hB : ∀ k < L, B (k+1)=σ k ((w k+e k)*B k))
    (hlegal : ∀ k < L, Q k ≠ 0)
    (hα : ∀ k < L, 0 ≤ a k ∧ a k ≤ 1)
    (hγ : ∀ k < L, 0 ≤ γ k)
    (hlip : ∀ k < L, ∀ u v, |σ k u-σ k v| ≤ γ k* |u-v|) :
    |X L-Q L| ≤ weightedBound
      (fun k => γ k*(|w k|+|e k|))
      (fun k => γ k* |w k*X k-(w k+e k)*B k|) L := by
  apply cross_terminal_loose
    (fun k => |Q k-B k|) (fun k => |X k-B k|) (fun k => |X k-Q k|)
    (fun k => γ k*(|w k|+|e k|)) (fun k => a k*γ k* |w k|)
    (fun k => γ k* |w k*X k-(w k+e k)*B k|) L
  · simp [hinitB,hinitQ]
  · simp [hinitB]
  · intro k hk; positivity
  · intro k hk; exact mul_nonneg (hγ k hk) (by positivity)
  · intro k hk
    have h1 := mul_le_mul_of_nonneg_right (hα k hk).2 (mul_nonneg (hγ k hk) (abs_nonneg (w k)))
    have h2 : 0 ≤ γ k* |e k| := mul_nonneg (hγ k hk) (abs_nonneg (e k))
    nlinarith
  · exact scalar_trajectory_recurrence w e a γ X B Q σ L hQ hB hlegal hα hγ hlip
  · intro k hk
    rw [hX k hk,hB k hk]
    exact hlip k hk _ _
  · have h := abs_add_le (X L-B L) (B L-Q L)
    have he : X L-B L+(B L-Q L)=X L-Q L := by ring
    rw [he,abs_sub_comm (B L) (Q L)] at h
    exact h

end
end QepV1
