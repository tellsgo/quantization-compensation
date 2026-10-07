import QepLinearIdentities
import QepLinearOrder






set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QepLinear
noncomputable section
open Matrix QepCorrected

variable {d e m : Type*} [Fintype d] [Fintype e] [Fintype m]
  [DecidableEq d] [DecidableEq e] [DecidableEq m]


theorem T8_error_congr (α : ℝ) (Z X : Mat d m) (P : Mat m m) (W : Mat e d)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Loewner (W * ((Tmix α Z X P - X) * (Tmix α Z X P - X)ᵀ) * Wᵀ)
      (W * ((Z - X) * (Z - X)ᵀ) * Wᵀ) :=
  Loewner.congr (T4_first_loewner α Z X P hs hp hz h0 (by linarith)) W


theorem T8_gram_congr (α : ℝ) (Z X : Mat d m) (P : Mat m m) (W : Mat e d)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Loewner (W * (Tmix α Z X P * (Tmix α Z X P)ᵀ) * Wᵀ)
      (W * ((1 - α) • (Z * Zᵀ) + α • (X * Xᵀ)) * Wᵀ) :=
  Loewner.congr (T4_second_loewner α Z X P hs hp hz h0 h1) W


theorem T9_multilayer
    (W : ℕ → Mat d d) (Ψ : ℕ → Mat d d → Mat d d)
    (hΨ : ∀ l, ∀ A B : Mat d d, Loewner A B → Loewner (Ψ l A) (Ψ l B))
    (α : ℕ → ℝ) (h0 : ∀ l, 0 ≤ α l) (h1 : ∀ l, α l ≤ 1)
    (S CQ GQ CB GB : ℕ → Mat d d)
    (hCQ : ∀ l, Loewner (CQ (l + 1)) (W l * CQ l * (W l)ᵀ + Ψ l (GQ l)))
    (hGQ : ∀ l, Loewner (GQ (l + 1))
      (W l * ((1 - α l) • GQ l + α l • S l) * (W l)ᵀ + Ψ l (GQ l)))
    (hCB : ∀ l, CB (l + 1) = W l * CB l * (W l)ᵀ + Ψ l (GB l))
    (hGB : ∀ l, GB (l + 1) = W l * GB l * (W l)ᵀ + Ψ l (GB l))
    (hS : ∀ l, Loewner (S l) (GB l))
    (hC0 : Loewner (CQ 0) (CB 0)) (hG0 : Loewner (GQ 0) (GB 0)) :
    ∀ l, Loewner (CQ l) (CB l) ∧ Loewner (GQ l) (GB l) := by
  intro l
  induction l with
  | zero => exact ⟨hC0, hG0⟩
  | succ l ih =>
    exact T6_order_propagation (W l) (Ψ l) (hΨ l) (α l) (h0 l) (h1 l)
      (CQ l) (GQ l) (CB l) (GB l) (S l) _ _ _ _
      (hCQ l) (hGQ l) (hCB l) (hGB l) ih.1 ih.2 (hS l)


theorem T9_multilayer_dep
    (n : ℕ → Type*) [∀ l, Fintype (n l)] [∀ l, DecidableEq (n l)]
    (W : ∀ l, Mat (n (l + 1)) (n l))
    (Ψ : ∀ l, Mat (n l) (n l) → Mat (n (l + 1)) (n (l + 1)))
    (hΨ : ∀ l, ∀ A B : Mat (n l) (n l), Loewner A B → Loewner (Ψ l A) (Ψ l B))
    (α : ℕ → ℝ) (h0 : ∀ l, 0 ≤ α l) (h1 : ∀ l, α l ≤ 1)
    (S CQ GQ CB GB : ∀ l, Mat (n l) (n l))
    (hCQ : ∀ l, Loewner (CQ (l + 1)) (W l * CQ l * (W l)ᵀ + Ψ l (GQ l)))
    (hGQ : ∀ l, Loewner (GQ (l + 1))
      (W l * ((1 - α l) • GQ l + α l • S l) * (W l)ᵀ + Ψ l (GQ l)))
    (hCB : ∀ l, CB (l + 1) = W l * CB l * (W l)ᵀ + Ψ l (GB l))
    (hGB : ∀ l, GB (l + 1) = W l * GB l * (W l)ᵀ + Ψ l (GB l))
    (hS : ∀ l, Loewner (S l) (GB l))
    (hC0 : Loewner (CQ 0) (CB 0)) (hG0 : Loewner (GQ 0) (GB 0)) :
    ∀ l, Loewner (CQ l) (CB l) ∧ Loewner (GQ l) (GB l) := by
  intro l
  induction l with
  | zero => exact ⟨hC0, hG0⟩
  | succ l ih =>
    exact T6_order_propagation (W l) (Ψ l) (hΨ l) (α l) (h0 l) (h1 l)
      (CQ l) (GQ l) (CB l) (GB l) (S l) _ _ _ _
      (hCQ l) (hGQ l) (hCB l) (hGB l) ih.1 ih.2 (hS l)


theorem T10_trace_le {A B : Mat d d} (h : Loewner A B) :
    Matrix.trace A ≤ Matrix.trace B := by
  unfold Loewner at h
  have := h.trace_nonneg
  rw [Matrix.trace_sub] at this
  linarith


theorem T10_multilayer_trace
    (W : ℕ → Mat d d) (Ψ : ℕ → Mat d d → Mat d d)
    (hΨ : ∀ l, ∀ A B : Mat d d, Loewner A B → Loewner (Ψ l A) (Ψ l B))
    (α : ℕ → ℝ) (h0 : ∀ l, 0 ≤ α l) (h1 : ∀ l, α l ≤ 1)
    (S CQ GQ CB GB : ℕ → Mat d d)
    (hCQ : ∀ l, Loewner (CQ (l + 1)) (W l * CQ l * (W l)ᵀ + Ψ l (GQ l)))
    (hGQ : ∀ l, Loewner (GQ (l + 1))
      (W l * ((1 - α l) • GQ l + α l • S l) * (W l)ᵀ + Ψ l (GQ l)))
    (hCB : ∀ l, CB (l + 1) = W l * CB l * (W l)ᵀ + Ψ l (GB l))
    (hGB : ∀ l, GB (l + 1) = W l * GB l * (W l)ᵀ + Ψ l (GB l))
    (hS : ∀ l, Loewner (S l) (GB l))
    (hC0 : Loewner (CQ 0) (CB 0)) (hG0 : Loewner (GQ 0) (GB 0)) :
    ∀ l, Matrix.trace (CQ l) ≤ Matrix.trace (CB l) := fun l =>
  T10_trace_le (T9_multilayer W Ψ hΨ α h0 h1 S CQ GQ CB GB hCQ hGQ hCB hGB hS hC0 hG0 l).1

end
end QepLinear
