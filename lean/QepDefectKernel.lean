import QepLinearOrder





set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QepComm
noncomputable section
open Matrix QepCorrected QepLinear

variable {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]


theorem convex_defect {G G' V S : Mat d d} (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (hG : Loewner G (G' + V)) (hS : Loewner S G') :
    Loewner ((1 - a) • G + a • S) (G' + (1 - a) • V) := by
  unfold Loewner at *
  have h := (hG.smul (show (0:ℝ) ≤ 1 - a by linarith)).add (hS.smul h0)
  have e : (1 - a) • (G' + V - G) + a • (G' - S) =
      G' + (1 - a) • V - ((1 - a) • G + a • S) := by
    module
  rwa [e] at h


theorem T5_step_C (F : Mat e d) (Ψ : Mat d d → Mat e e)
    (hadd : ∀ A B : Mat d d, Ψ (A + B) = Ψ A + Ψ B)
    (hΨ : ∀ A B : Mat d d, Loewner A B → Loewner (Ψ A) (Ψ B))
    (C C' K G G' V : Mat d d) (A : Mat e e)
    (hC : Loewner C (C' + K)) (hG : Loewner G (G' + V)) :
    Loewner (F * C * Fᵀ + Ψ G + A)
      ((F * C' * Fᵀ + Ψ G') + (F * K * Fᵀ + Ψ V + A)) := by
  have h := ((hC.congr F).add (hΨ _ _ hG)).add (Loewner.of_eq (rfl : A = A))
  refine h.trans (Loewner.of_eq ?_)
  rw [hadd, Matrix.mul_add, Matrix.add_mul]
  abel


theorem T5_step_G (F : Mat e d) (Ψ : Mat d d → Mat e e)
    (hadd : ∀ A B : Mat d d, Ψ (A + B) = Ψ A + Ψ B)
    (hΨ : ∀ A B : Mat d d, Loewner A B → Loewner (Ψ A) (Ψ B))
    (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (G G' V S : Mat d d) (B : Mat e e)
    (hG : Loewner G (G' + V)) (hS : Loewner S G') :
    Loewner (F * ((1 - a) • G + a • S) * Fᵀ + Ψ G + B)
      ((F * G' * Fᵀ + Ψ G') + ((1 - a) • (F * V * Fᵀ) + Ψ V + B)) := by
  have h := (((convex_defect a h0 h1 hG hS).congr F).add (hΨ _ _ hG)).add
    (Loewner.of_eq (rfl : B = B))
  refine h.trans (Loewner.of_eq ?_)
  rw [hadd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  abel


theorem T5_multilayer
    (F : ℕ → Mat d d) (Ψ : ℕ → Mat d d → Mat d d)
    (hadd : ∀ l, ∀ A B : Mat d d, Ψ l (A + B) = Ψ l A + Ψ l B)
    (hΨ : ∀ l, ∀ A B : Mat d d, Loewner A B → Loewner (Ψ l A) (Ψ l B))
    (a : ℕ → ℝ) (h0 : ∀ l, 0 ≤ a l) (h1 : ∀ l, a l ≤ 1)
    (S CQ GQ CB GB K V A B : ℕ → Mat d d)
    (hCQ : ∀ l, Loewner (CQ (l + 1)) (F l * CQ l * (F l)ᵀ + Ψ l (GQ l) + A l))
    (hGQ : ∀ l, Loewner (GQ (l + 1))
      (F l * ((1 - a l) • GQ l + a l • S l) * (F l)ᵀ + Ψ l (GQ l) + B l))
    (hCB : ∀ l, CB (l + 1) = F l * CB l * (F l)ᵀ + Ψ l (GB l))
    (hGB : ∀ l, GB (l + 1) = F l * GB l * (F l)ᵀ + Ψ l (GB l))
    (hK : ∀ l, K (l + 1) = F l * K l * (F l)ᵀ + Ψ l (V l) + A l)
    (hV : ∀ l, V (l + 1) = (1 - a l) • (F l * V l * (F l)ᵀ) + Ψ l (V l) + B l)
    (hS : ∀ l, Loewner (S l) (GB l))
    (hC0 : Loewner (CQ 0) (CB 0 + K 0)) (hG0 : Loewner (GQ 0) (GB 0 + V 0)) :
    ∀ l, Loewner (CQ l) (CB l + K l) ∧ Loewner (GQ l) (GB l + V l) := by
  intro l
  induction l with
  | zero => exact ⟨hC0, hG0⟩
  | succ l ih =>
    rw [hCB l, hGB l, hK l, hV l]
    exact ⟨(hCQ l).trans (T5_step_C (F l) (Ψ l) (hadd l) (hΨ l) _ _ _ _ _ _ (A l) ih.1 ih.2),
      (hGQ l).trans (T5_step_G (F l) (Ψ l) (hadd l) (hΨ l) (a l) (h0 l) (h1 l)
        _ _ _ (S l) (B l) ih.2 (hS l))⟩


theorem T5_multilayer_dep
    (n : ℕ → Type*) [∀ l, Fintype (n l)] [∀ l, DecidableEq (n l)]
    (F : ∀ l, Mat (n (l + 1)) (n l))
    (Ψ : ∀ l, Mat (n l) (n l) → Mat (n (l + 1)) (n (l + 1)))
    (hadd : ∀ l, ∀ A B : Mat (n l) (n l), Ψ l (A + B) = Ψ l A + Ψ l B)
    (hΨ : ∀ l, ∀ A B : Mat (n l) (n l), Loewner A B → Loewner (Ψ l A) (Ψ l B))
    (a : ℕ → ℝ) (h0 : ∀ l, 0 ≤ a l) (h1 : ∀ l, a l ≤ 1)
    (S CQ GQ CB GB K V : ∀ l, Mat (n l) (n l))
    (A B : ∀ l, Mat (n (l + 1)) (n (l + 1)))
    (hCQ : ∀ l, Loewner (CQ (l + 1)) (F l * CQ l * (F l)ᵀ + Ψ l (GQ l) + A l))
    (hGQ : ∀ l, Loewner (GQ (l + 1))
      (F l * ((1 - a l) • GQ l + a l • S l) * (F l)ᵀ + Ψ l (GQ l) + B l))
    (hCB : ∀ l, CB (l + 1) = F l * CB l * (F l)ᵀ + Ψ l (GB l))
    (hGB : ∀ l, GB (l + 1) = F l * GB l * (F l)ᵀ + Ψ l (GB l))
    (hK : ∀ l, K (l + 1) = F l * K l * (F l)ᵀ + Ψ l (V l) + A l)
    (hV : ∀ l, V (l + 1) = (1 - a l) • (F l * V l * (F l)ᵀ) + Ψ l (V l) + B l)
    (hS : ∀ l, Loewner (S l) (GB l))
    (hC0 : Loewner (CQ 0) (CB 0 + K 0)) (hG0 : Loewner (GQ 0) (GB 0 + V 0)) :
    ∀ l, Loewner (CQ l) (CB l + K l) ∧ Loewner (GQ l) (GB l + V l) := by
  intro l
  induction l with
  | zero => exact ⟨hC0, hG0⟩
  | succ l ih =>
    rw [hCB l, hGB l, hK l, hV l]
    exact ⟨(hCQ l).trans (T5_step_C (F l) (Ψ l) (hadd l) (hΨ l) _ _ _ _ _ _ (A l) ih.1 ih.2),
      (hGQ l).trans (T5_step_G (F l) (Ψ l) (hadd l) (hΨ l) (a l) (h0 l) (h1 l)
        _ _ _ (S l) (B l) ih.2 (hS l))⟩

end
end QepComm
