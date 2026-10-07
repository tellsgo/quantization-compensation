import QepSharedE
import Mathlib




set_option autoImplicit false
namespace QepDitherFinite
noncomputable section
open QepSharedE

variable {Ω Ω₁ Ω₂ : Type*} [Fintype Ω] [Fintype Ω₁] [Fintype Ω₂]

def displacement (alpha w1 w2 x r1 r2 : ℝ) : ℝ :=
  (1-alpha)*w2*r1*x + r2*(w1+r1)*x

theorem trace_displacement (alpha1 alpha w1 w2 x r1 r2 : ℝ)
    (hx : x ≠ 0) (hr : w1+r1 ≠ 0) :
    (qepTrace ⟨w1,w2,x,1,1⟩ ⟨r1,r2⟩ alpha1 alpha).output -
      teacherOutput ⟨w1,w2,x,1,1⟩ = displacement alpha w1 w2 x r1 r2 := by
  have hfirst : corrected alpha1 w1 x x = w1 := by simp [corrected]
  simp only [qepTrace,hfirst,teacherOutput,teacher2,activation]
  unfold corrected gram displacement
  field_simp
  <;> ring

theorem sum_affine_square (p r : Ω → ℝ) (u v sigmaSq : ℝ)
    (hmass : ∑ i, p i = 1) (hmean : ∑ i, p i*r i = 0)
    (hsecond : ∑ i, p i*(r i)^2 = sigmaSq) :
    (∑ i, p i*(u+v*r i)^2) = u^2 + v^2*sigmaSq := by
  calc
    (∑ i, p i*(u+v*r i)^2) =
        u^2*(∑ i,p i)+(2*u*v)*(∑ i,p i*r i)+v^2*(∑ i,p i*(r i)^2) := by
      rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
        ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hmass,hmean,hsecond]; ring

theorem product_mean_square (p₁ : Ω₁ → ℝ) (p₂ : Ω₂ → ℝ)
    (r₁ : Ω₁ → ℝ) (r₂ : Ω₂ → ℝ) (alpha w1 w2 x sigmaSq : ℝ)
    (hm1 : ∑ i,p₁ i = 1) (hm2 : ∑ j,p₂ j = 1)
    (hz1 : ∑ i,p₁ i*r₁ i = 0) (hz2 : ∑ j,p₂ j*r₂ j = 0)
    (hs1 : ∑ i,p₁ i*(r₁ i)^2 = sigmaSq)
    (hs2 : ∑ j,p₂ j*(r₂ j)^2 = sigmaSq) :
    (∑ i, ∑ j, p₁ i*p₂ j*(displacement alpha w1 w2 x (r₁ i) (r₂ j))^2) =
      x^2*sigmaSq*((1-alpha)^2*w2^2+w1^2+sigmaSq) := by
  have inner (i : Ω₁) :
      (∑ j,p₂ j*(displacement alpha w1 w2 x (r₁ i) (r₂ j))^2) =
      ((1-alpha)*w2*r₁ i*x)^2 + ((w1+r₁ i)*x)^2*sigmaSq := by
    convert sum_affine_square p₂ r₂ ((1-alpha)*w2*r₁ i*x)
      ((w1+r₁ i)*x) sigmaSq hm2 hz2 hs2 using 1
    apply Finset.sum_congr rfl
    intro j hj
    unfold displacement
    ring
  calc
    _ = ∑ i,p₁ i*(((1-alpha)*w2*r₁ i*x)^2+((w1+r₁ i)*x)^2*sigmaSq) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← inner,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ((1-alpha)*w2*x)^2*(∑ i,p₁ i*(r₁ i)^2) +
          x^2*sigmaSq*(∑ i,p₁ i*(w1+1*r₁ i)^2) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [hs1,sum_affine_square p₁ r₁ w1 1 sigmaSq hm1 hz1 hs1]
      ring

theorem actual_network_mean_square (p₁ : Ω₁ → ℝ) (p₂ : Ω₂ → ℝ)
    (r₁ : Ω₁ → ℝ) (r₂ : Ω₂ → ℝ) (alpha1 alpha w1 w2 x sigmaSq : ℝ)
    (hp1 : ∀ i,0 ≤ p₁ i) (hp2 : ∀ j,0 ≤ p₂ j)
    (hm1 : ∑ i,p₁ i = 1) (hm2 : ∑ j,p₂ j = 1)
    (hz1 : ∑ i,p₁ i*r₁ i = 0) (hz2 : ∑ j,p₂ j*r₂ j = 0)
    (hs1 : ∑ i,p₁ i*(r₁ i)^2 = sigmaSq)
    (hs2 : ∑ j,p₂ j*(r₂ j)^2 = sigmaSq)
    (hx : x ≠ 0) (hr : ∀ i,p₁ i ≠ 0 → w1+r₁ i ≠ 0) :
    (∑ i, ∑ j, p₁ i*p₂ j*
      ((qepTrace ⟨w1,w2,x,1,1⟩ ⟨r₁ i,r₂ j⟩ alpha1 alpha).output-
       teacherOutput ⟨w1,w2,x,1,1⟩)^2) =
      x^2*sigmaSq*((1-alpha)^2*w2^2+w1^2+sigmaSq) := by
  rw [← product_mean_square p₁ p₂ r₁ r₂ alpha w1 w2 x sigmaSq hm1 hm2 hz1 hz2 hs1 hs2]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : p₁ i = 0
  · simp [h]
  · rw [trace_displacement alpha1 alpha w1 w2 x (r₁ i) (r₂ j) hx (hr i h)]

theorem actual_terminal_mean_square (p₁ : Ω₁ → ℝ) (p₂ : Ω₂ → ℝ)
    (r₁ : Ω₁ → ℝ) (r₂ : Ω₂ → ℝ) (alpha1 alpha w1 w2 x sigmaSq : ℝ)
    (hp1 : ∀ i,0 ≤ p₁ i) (hp2 : ∀ j,0 ≤ p₂ j)
    (hm1 : ∑ i,p₁ i = 1) (hm2 : ∑ j,p₂ j = 1)
    (hz1 : ∑ i,p₁ i*r₁ i = 0) (hz2 : ∑ j,p₂ j*r₂ j = 0)
    (hs1 : ∑ i,p₁ i*(r₁ i)^2 = sigmaSq)
    (hs2 : ∑ j,p₂ j*(r₂ j)^2 = sigmaSq)
    (hx : x ≠ 0) (hr : ∀ i,p₁ i ≠ 0 → w1+r₁ i ≠ 0) :
    (∑ i, ∑ j, p₁ i*p₂ j*
      (terminalError ⟨w1,w2,x,1,1⟩
        (qepTrace ⟨w1,w2,x,1,1⟩ ⟨r₁ i,r₂ j⟩ alpha1 alpha))^2) =
      x^2*sigmaSq*((1-alpha)^2*w2^2+w1^2+sigmaSq) := by
  rw [← actual_network_mean_square p₁ p₂ r₁ r₂ alpha1 alpha w1 w2 x sigmaSq
    hp1 hp2 hm1 hm2 hz1 hz2 hs1 hs2 hx hr]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [terminalError,sq_abs]
  ring

theorem mean_square_nonincreasing (w1 w2 x sigmaSq a b : ℝ)
    (hs : 0 ≤ sigmaSq) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    x^2*sigmaSq*((1-b)^2*w2^2+w1^2+sigmaSq) ≤
      x^2*sigmaSq*((1-a)^2*w2^2+w1^2+sigmaSq) := by
  have hh : (1-b)^2 ≤ (1-a)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg w2)
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (sq_nonneg x) hs)

end
end QepDitherFinite
