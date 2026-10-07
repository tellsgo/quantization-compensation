import QepX1NetworkMoments
import QepV3Order

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace QepX1
noncomputable section
open QepCorrected QepGram QepV3
open scoped BigOperators
variable {Ω m n t : Type*} [Fintype Ω] [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]

theorem mean_psdLe_support (p : Ω → ℝ) (F G : Ω → Mat n n)
    (hp : ∀ ω,0 ≤ p ω) (h : ∀ ω,p ω ≠ 0 → PSDLe (F ω) (G ω)) :
    PSDLe (mean p F) (mean p G) := by
  change (mean p G-mean p F).PosSemidef
  rw [← mean_sub]
  unfold mean
  apply Matrix.posSemidef_sum
  intro ω _
  by_cases hz : p ω=0
  · simp only [hz,zero_smul]
    exact Matrix.PosSemidef.zero
  · exact (h ω hz).smul (hp ω)

theorem psdLe_congruence (W : Mat m n) {A B : Mat n n} (h : PSDLe A B) :
    PSDLe (W*A*W.transpose) (W*B*W.transpose) := by
  have hh := h.mul_mul_conjTranspose_same W
  simpa only [PSDLe,Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_sub,Matrix.sub_mul] using hh

theorem psdLe_add {A B C D : Mat n n} (hAB : PSDLe A B) (hCD : PSDLe C D) :
    PSDLe (A+C) (B+D) := by
  have hh := hAB.add hCD
  have he : (B-A)+(D-C)=(B+D)-(A+C) := by abel
  change ((B+D)-(A+C)).PosSemidef
  rw [← he]
  exact hh

theorem psdLe_linear_map (Ψ : Mat n n →ₗ[ℝ] Mat m m)
    (hΨ : ∀ V : Mat n n,V.PosSemidef → (Ψ V).PosSemidef)
    {A B : Mat n n} (h : PSDLe A B) : PSDLe (Ψ A) (Ψ B) := by
  have hh := hΨ (B-A) h
  simpa only [PSDLe,map_sub] using hh



theorem actual_qep_error_le_of_pointwise {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (Z : Ω → Mat n t) (W : Mat m n) (X : Mat n t) (a : ℝ)
    (Ψ : Mat n n →ₗ[ℝ] Mat m m) (law : FiniteLaw p)
    (hZpast : Past history k Z) (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → IsUnit (gram (Z ω)).det)
    (hpoint : ∀ ω,p ω ≠ 0 →
      PSDLe ((correctedInput X (Z ω) a-X)*(correctedInput X (Z ω) a-X).transpose)
        ((Z ω-X)*(Z ω-X).transpose)) :
    PSDLe (mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω-W*X).transpose))
      (W*mean p (fun ω => (Z ω-X)*(Z ω-X).transpose)*W.transpose+
        Ψ (mean p (fun ω => Z ω*(Z ω).transpose))) := by
  rw [actual_qep_error_moment history k p E Z W X a Ψ hZpast hfirst hsecond hgram]
  exact psdLe_add (psdLe_congruence W (mean_psdLe_support p _ _ law.nonnegative hpoint))
    (psdLe_refl _)



theorem actual_qep_output_le_of_pointwise {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (Z : Ω → Mat n t) (W : Mat m n) (X : Mat n t) (a : ℝ)
    (Ψ : Mat n n →ₗ[ℝ] Mat m m) (law : FiniteLaw p)
    (hZpast : Past history k Z) (hfirst : ConditionalMeanZero history k p E)
    (hsecond : ConditionalSecondPSD history k p E Ψ)
    (hgram : ∀ ω,p ω ≠ 0 → IsUnit (gram (Z ω)).det)
    (hpoint : ∀ ω,p ω ≠ 0 →
      PSDLe (correctedInput X (Z ω) a*(correctedInput X (Z ω) a).transpose)
        ((1-a) • (Z ω*(Z ω).transpose)+a • (X*X.transpose))) :
    PSDLe (mean p (fun ω => ((correctedWeight W X (Z ω) a+E ω)*Z ω)*
      ((correctedWeight W X (Z ω) a+E ω)*Z ω).transpose))
      (W*((1-a) • mean p (fun ω => Z ω*(Z ω).transpose)+a • (X*X.transpose))*W.transpose+
        Ψ (mean p (fun ω => Z ω*(Z ω).transpose))) := by
  rw [actual_qep_output_moment history k p E Z W X a Ψ hZpast hfirst hsecond hgram]
  have hh := mean_psdLe_support p _ _ law.nonnegative hpoint
  simp only [mean_add,mean_smul,mean_const p _ law.mass] at hh
  exact psdLe_add (psdLe_congruence W hh) (psdLe_refl _)

end
end QepX1
