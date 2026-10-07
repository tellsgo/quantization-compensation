import QepCorrected





set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QepLinear
noncomputable section
open Matrix QepCorrected

variable {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]


def Loewner (A B : Mat d d) : Prop := (B - A).PosSemidef

theorem Loewner.trans {A B C : Mat d d} (h1 : Loewner A B) (h2 : Loewner B C) :
    Loewner A C := by
  unfold Loewner at *
  have h := h2.add h1
  have e : C - B + (B - A) = C - A := by abel
  rwa [e] at h

theorem Loewner.of_eq {A B : Mat d d} (h : A = B) : Loewner A B := by
  unfold Loewner
  rw [h, sub_self]
  exact Matrix.PosSemidef.zero

theorem Loewner.add {A B C D : Mat d d} (h1 : Loewner A B) (h2 : Loewner C D) :
    Loewner (A + C) (B + D) := by
  unfold Loewner at *
  have h := h1.add h2
  have e : B - A + (D - C) = B + D - (A + C) := by abel
  rwa [e] at h


theorem Loewner.congr {A B : Mat d d} (h : Loewner A B) (W : Mat e d) :
    Loewner (W * A * Wᵀ) (W * B * Wᵀ) := by
  unfold Loewner at *
  have h' := h.mul_mul_conjTranspose_same W
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  have e : W * (B - A) * Wᵀ = W * B * Wᵀ - W * A * Wᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [e] at h'


theorem Loewner.convex {A S B : Mat d d} (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (hA : Loewner A B) (hS : Loewner S B) :
    Loewner ((1 - α) • A + α • S) B := by
  unfold Loewner at *
  have h := (hA.smul (show (0:ℝ) ≤ 1 - α by linarith)).add (hS.smul h0)
  have e : (1 - α) • (B - A) + α • (B - S) = B - ((1 - α) • A + α • S) := by
    simp only [smul_sub]; module
  rwa [e] at h


theorem T6_order_propagation
    (W : Mat e d) (Ψ : Mat d d → Mat e e)
    (hΨ : ∀ A B : Mat d d, Loewner A B → Loewner (Ψ A) (Ψ B))
    (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (CQ GQ CB GB S : Mat d d) (CQ' GQ' CB' GB' : Mat e e)
    (hCQ' : Loewner CQ' (W * CQ * Wᵀ + Ψ GQ))
    (hGQ' : Loewner GQ' (W * ((1 - α) • GQ + α • S) * Wᵀ + Ψ GQ))
    (hCB' : CB' = W * CB * Wᵀ + Ψ GB)
    (hGB' : GB' = W * GB * Wᵀ + Ψ GB)
    (hC : Loewner CQ CB) (hG : Loewner GQ GB) (hS : Loewner S GB) :
    Loewner CQ' CB' ∧ Loewner GQ' GB' := by
  subst hCB' hGB'
  exact ⟨hCQ'.trans ((hC.congr W).add (hΨ _ _ hG)),
    hGQ'.trans (((Loewner.convex α h0 h1 hG hS).congr W).add (hΨ _ _ hG))⟩

end
end QepLinear
