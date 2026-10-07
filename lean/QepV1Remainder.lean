import QepV1Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV1
noncomputable section
open scoped BigOperators
open QepCorrected QepGram


theorem weightedBound_mono (a b c d : ℕ → ℝ) (L : ℕ)
    (ha : ∀ k < L, 0 ≤ a k) (hc : ∀ k < L, 0 ≤ c k)
    (hab : ∀ k < L, a k ≤ b k) (hcd : ∀ k < L, c k ≤ d k) :
    weightedBound a c L ≤ weightedBound b d L := by
  apply recurrence_bound (weightedBound a c) b d L (by simp [weightedBound])
  · intro k hk; exact (ha k hk).trans (hab k hk)
  · intro k hk
    have hn := weightedBound_nonneg a c k (fun j hj => ha j (by omega)) (fun j hj => hc j (by omega))
    have h1 := mul_le_mul_of_nonneg_right (hab k hk) hn
    change a k*weightedBound a c k+c k ≤ b k*weightedBound a c k+d k
    exact add_le_add h1 (hcd k hk)

theorem weightedBound_smul (a c : ℕ → ℝ) (s : ℝ) (L : ℕ) :
    weightedBound a (fun k => s*c k) L = s*weightedBound a c L := by
  induction L with
  | zero => simp [weightedBound]
  | succ k ih => simp only [weightedBound,ih]; ring


def remainderConstant (a0 f cEnv : ℕ → ℝ) (L : ℕ) : ℝ :=
  weightedBound (fun k => a0 k+f k)
    (fun k => f k*weightedBound (fun j => a0 j+f j) cEnv k) L



theorem weightedBound_diff_quadratic (a0 a f c cEnv : ℕ → ℝ) (L : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha0 : ∀ k < L, 0 ≤ a0 k) (hf : ∀ k < L, 0 ≤ f k)
    (hc : ∀ k < L, 0 ≤ c k) (_hEnv : ∀ k < L, 0 ≤ cEnv k)
    (ha : ∀ k < L, a0 k ≤ a k ∧ a k ≤ a0 k+t*f k)
    (hres : ∀ k < L, c k ≤ t*cEnv k) :
    0 ≤ weightedBound a c L-weightedBound a0 c L ∧
    weightedBound a c L-weightedBound a0 c L ≤
      t^2*remainderConstant a0 f cEnv L := by
  let A := fun k => a0 k+f k
  let V := weightedBound A cEnv
  let Δ := fun k => weightedBound a c k-weightedBound a0 c k
  have hA : ∀ k < L, 0 ≤ A k := fun k hk => add_nonneg (ha0 k hk) (hf k hk)
  have hDelta : ∀ k ≤ L, 0 ≤ Δ k := by
    intro k hk
    apply sub_nonneg.mpr
    exact weightedBound_mono a0 a c c k (fun j hj => ha0 j (by omega))
      (fun j hj => hc j (by omega)) (fun j hj => (ha j (by omega)).1) (fun j hj => le_rfl)
  have hU : ∀ k ≤ L, weightedBound a0 c k ≤ t*V k := by
    intro k hk
    change weightedBound a0 c k ≤ t*weightedBound A cEnv k
    rw [← weightedBound_smul]
    apply weightedBound_mono a0 A c (fun j => t*cEnv j) k
    · intro j hj; exact ha0 j (by omega)
    · intro j hj; exact hc j (by omega)
    · intro j hj; dsimp [A]; linarith [hf j (by omega)]
    · intro j hj; exact hres j (by omega)
  have hrec : Δ L ≤ weightedBound A (fun k => t^2*(f k*V k)) L := by
    apply recurrence_bound Δ A _ L (by simp [Δ,weightedBound]) hA
    intro k hk
    have haA : a k ≤ A k := by
      have hh := (ha k hk).2
      have hf0 := hf k hk
      dsimp [A]
      nlinarith
    have hfirst := mul_le_mul_of_nonneg_right haA (hDelta k (by omega))
    have hU0 := weightedBound_nonneg a0 c k (fun j hj => ha0 j (by omega)) (fun j hj => hc j (by omega))
    have hsecond : (a k-a0 k)*weightedBound a0 c k ≤ (t*f k)*(t*V k) := by
      apply mul_le_mul (by linarith [(ha k hk).2]) (hU k (by omega)) hU0
      exact mul_nonneg ht0 (hf k hk)
    have he : Δ (k+1)=a k*Δ k+(a k-a0 k)*weightedBound a0 c k := by
      dsimp [Δ]
      simp only [weightedBound]
      ring
    rw [he]
    calc
      _ ≤ A k*Δ k+(t*f k)*(t*V k) := add_le_add hfirst hsecond
      _ = A k*Δ k+t^2*(f k*V k) := by ring
  rw [weightedBound_smul] at hrec
  exact ⟨hDelta L le_rfl,hrec⟩

end
end QepV1
