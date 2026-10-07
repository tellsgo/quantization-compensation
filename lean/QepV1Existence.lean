import QepV1Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV1
noncomputable section
open QepCorrected QepGram Filter Topology
open scoped Matrix.Norms.Frobenius

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]


theorem continuousAt_rect_mul {A : ℝ → Mat m n} {B : ℝ → Mat n p} {t : ℝ}
    (hA : ContinuousAt A t) (hB : ContinuousAt B t) :
    ContinuousAt (fun s => A s*B s) t := by
  exact (continuous_fst.matrix_mul continuous_snd).continuousAt.comp (hA.prodMk hB)

theorem frob_lipschitz_continuous (σ : Mat m n → Mat m n) (γ : ℝ)
    (hlip : ∀ U V, frobNorm (σ U-σ V) ≤ γ*frobNorm (U-V)) : Continuous σ := by
  apply (LipschitzWith.of_dist_le' (K := γ) ?_).continuous
  intro U V
  simpa only [dist_eq_norm, frobNorm] using hlip U V



def qepRun (d : ℕ → ℕ) (N : ℕ)
    (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (X : (k : ℕ) → Mat (Fin (d k)) (Fin N)) (α : ℕ → ℝ)
    (σ : (k : ℕ) → Mat (Fin (d (k+1))) (Fin N) → Mat (Fin (d (k+1))) (Fin N))
    (E : ℝ → (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k))) (s : ℝ) :
    (k : ℕ) → Mat (Fin (d k)) (Fin N)
  | 0 => X 0
  | k+1 => σ k ((correctedWeight (W k) (X k) (qepRun d N W X α σ E s k) (α k)+E s k)*
      qepRun d N W X α σ E s k)

variable (d : ℕ → ℕ) (N L : ℕ)
variable (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
variable (X : (k : ℕ) → Mat (Fin (d k)) (Fin N)) (α : ℕ → ℝ)
variable (σ : (k : ℕ) → Mat (Fin (d (k+1))) (Fin N) → Mat (Fin (d (k+1))) (Fin N))
variable (E : ℝ → (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))


theorem qepRun_zero
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k)) (hE : ∀ k < L, E 0 k=0) :
    ∀ k ≤ L, qepRun d N W X α σ E 0 k=X k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qepRun,ih (by omega),hE k (by omega)]
    simpa [correctedWeight,correction] using (hX k (by omega)).symm



theorem qepRun_continuousAt_zero
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k)) (hE0 : ∀ k < L, E 0 k=0)
    (hE : ∀ k < L, ContinuousAt (fun s => E s k) 0)
    (hσ : ∀ k < L, Continuous (σ k))
    (hrow : ∀ k < L, LinearIndependent ℝ (X k).row) :
    ∀ k ≤ L, ContinuousAt (fun s => qepRun d N W X α σ E s k) 0 := by
  intro k hk
  induction k with
  | zero => exact continuousAt_const
  | succ k ih =>
    have hq := ih (by omega)
    have hz := qepRun_zero d N L W X α σ E hX hE0 k (by omega)
    have hqt : ContinuousAt (fun s => (qepRun d N W X α σ E s k).transpose) 0 :=
      continuous_id.matrix_transpose.continuousAt.comp hq
    have hg : ContinuousAt (fun s => gram (qepRun d N W X α σ E s k)) 0 :=
      continuousAt_rect_mul hq hqt
    have hunit := gram_isUnit_det_of_full_row_rank (X k) (hrow k (by omega))
    have hne : (gram (qepRun d N W X α σ E 0 k)).det ≠ 0 := by
      rw [hz]; exact hunit.ne_zero
    have hinv : ContinuousAt (fun s => (gram (qepRun d N W X α σ E s k))⁻¹) 0 := by
      apply (continuousAt_matrix_inv _ ?_).comp hg
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hne
    have hdiff : ContinuousAt (fun s => X k-qepRun d N W X α σ E s k) 0 := continuousAt_const.sub hq
    have hc1 := continuousAt_rect_mul (A := fun _ : ℝ => W k) continuousAt_const hdiff
    have hc2 := continuousAt_rect_mul hc1 hqt
    have hc3 := continuousAt_rect_mul hc2 hinv
    have hweight : ContinuousAt
        (fun s => correctedWeight (W k) (X k) (qepRun d N W X α σ E s k) (α k)+E s k) 0 :=
      (continuousAt_const.add (hc3.const_smul (α k))).add (hE k (by omega))
    exact (hσ k (by omega)).continuousAt.comp (continuousAt_rect_mul hweight hq)



theorem qepRun_eventually_legal
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k)) (hE0 : ∀ k < L, E 0 k=0)
    (hE : ∀ k < L, ContinuousAt (fun s => E s k) 0)
    (hσ : ∀ k < L, Continuous (σ k))
    (hrow : ∀ k < L, LinearIndependent ℝ (X k).row) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k < L, IsUnit (gram (qepRun d N W X α σ E s k)).det := by
  have hall : ∀ k : Fin L, ∀ᶠ s in 𝓝 (0 : ℝ),
      IsUnit (gram (qepRun d N W X α σ E s k)).det := by
    intro k
    have hq := qepRun_continuousAt_zero d N L W X α σ E hX hE0 hE hσ hrow k (by omega)
    have hqt := continuous_id.matrix_transpose.continuousAt.comp hq
    have hg := continuousAt_rect_mul hq hqt
    have hd := continuous_id.matrix_det.continuousAt.comp hg
    have hne : (gram (qepRun d N W X α σ E 0 k)).det ≠ 0 := by
      rw [qepRun_zero d N L W X α σ E hX hE0 k (by omega)]
      exact (gram_isUnit_det_of_full_row_rank (X k) (hrow k k.isLt)).ne_zero
    have hev := hd.eventually_ne hne
    filter_upwards [hev] with s hs
    exact isUnit_iff_ne_zero.mpr hs
  have h := Filter.eventually_all.mpr hall
  filter_upwards [h] with s hs
  intro k hk
  exact hs ⟨k,hk⟩


theorem qepRun_exists_legal_radius
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k)) (hE0 : ∀ k < L, E 0 k=0)
    (hE : ∀ k < L, ContinuousAt (fun s => E s k) 0)
    (hσ : ∀ k < L, Continuous (σ k))
    (hrow : ∀ k < L, LinearIndependent ℝ (X k).row) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| < ε →
      ∀ k < L, IsUnit (gram (qepRun d N W X α σ E s k)).det := by
  have h := qepRun_eventually_legal d N L W X α σ E hX hE0 hE hσ hrow
  rcases Metric.mem_nhds_iff.mp h with ⟨ε,hε,hh⟩
  refine ⟨ε,hε,?_⟩
  intro s hs
  exact hh (by simpa [Metric.mem_ball,Real.dist_eq] using hs)



theorem qepRun_linear_exists_legal_radius
    (F : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k))) (γ : ℕ → ℝ)
    (hX : ∀ k < L, X (k+1)=σ k (W k*X k))
    (hlip : ∀ k < L, ∀ U V, frobNorm (σ k U-σ k V) ≤ γ k*frobNorm (U-V))
    (hrow : ∀ k < L, LinearIndependent ℝ (X k).row) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| < ε → ∀ k < L,
      IsUnit (gram (qepRun d N W X α σ (fun s k => s • F k) s k)).det := by
  apply qepRun_exists_legal_radius d N L W X α σ (fun s k => s • F k) hX
  · intro k hk; simp
  · intro k hk; exact continuousAt_id.smul continuousAt_const
  · intro k hk; exact frob_lipschitz_continuous (σ k) (γ k) (hlip k hk)
  · exact hrow

end
end QepV1
