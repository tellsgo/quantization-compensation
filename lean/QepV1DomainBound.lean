import QepV1Envelope
import QepV1Existence

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV1
noncomputable section
open QepCorrected QepGram
open scoped Matrix.Norms.Frobenius


def baseRun (d : ℕ → ℕ) (N : ℕ)
    (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (X : (k : ℕ) → Mat (Fin (d k)) (Fin N))
    (σ : (k : ℕ) → Mat (Fin (d (k+1))) (Fin N) → Mat (Fin (d (k+1))) (Fin N))
    (E : ℝ → (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k))) (s : ℝ) :
    (k : ℕ) → Mat (Fin (d k)) (Fin N)
  | 0 => X 0
  | k+1 => σ k ((W k+E s k)*baseRun d N W X σ E s k)




theorem actual_network_exists_first_order_radius
    (d : ℕ → ℕ) (N L : ℕ)
    (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (X : (k : ℕ) → Mat (Fin (d k)) (Fin N)) (α γ f : ℕ → ℝ)
    (σ : (k : ℕ) → Mat (Fin (d (k+1))) (Fin N) → Mat (Fin (d (k+1))) (Fin N))
    (E : ℝ → (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k))
    (hE0 : ∀ k < L, E 0 k=0)
    (hEc : ∀ k < L, ContinuousAt (fun s => E s k) 0)
    (hE : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ k < L, spectralNorm (E s k) ≤ s*f k)
    (hf : ∀ k < L, 0 ≤ f k)
    (hα : ∀ k < L, 0 ≤ α k ∧ α k ≤ 1) (hγ : ∀ k < L, 0 ≤ γ k)
    (hlip : ∀ k < L, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V))
    (hrow : ∀ k < L, LinearIndependent ℝ (X k).row) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ s : ℝ, 0 ≤ s → s < ε →
      (∀ k < L, IsUnit (gram (qepRun d N W X α σ E s k)).det) ∧
      frobNorm (X L-qepRun d N W X α σ E s L) ≤
        weightedBound (fun k => γ k*spectralNorm (W k))
          (fun k => γ k*frobNorm (W k*X k-(W k+E s k)*baseRun d N W X σ E s k)) L +
        s^2*matrixRemainderConstant d N L W X γ f := by
  have hσ : ∀ k < L, Continuous (σ k) :=
    fun k hk => frob_lipschitz_continuous (σ k) (γ k) (hlip k hk)
  obtain ⟨δ,hδ,hlegal⟩ := qepRun_exists_legal_radius d N L W X α σ E hX hE0 hEc hσ hrow
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro s hs hsε
  have hs1 : s ≤ 1 := le_trans (le_of_lt hsε) (min_le_right _ _)
  have hgram := hlegal s (by rw [abs_of_nonneg hs]; exact lt_of_lt_of_le hsε (min_le_left _ _))
  refine ⟨hgram,?_⟩
  apply matrix_actual_first_order_bound d N L W (E s) X
    (baseRun d N W X σ E s) (qepRun d N W X α σ E s) α γ f σ s hs hs1 hf (hE s hs hs1)
  · rfl
  · rfl
  · exact hX
  · intro k hk; rfl
  · intro k hk; rfl
  · exact hgram
  · exact hα
  · exact hγ
  · exact hlip

end
end QepV1
