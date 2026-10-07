import QepCorrected











set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace QepMargin
noncomputable section
open scoped BigOperators
open QepCorrected




theorem radius_nonneg (w e x r : ℕ → ℝ) (hw : ∀ l, 0 ≤ w l) (he : ∀ l, 0 ≤ e l)
    (hx : ∀ l, 0 ≤ x l) (hr0 : r 0 = 0)
    (hr : ∀ l, r (l+1) = (w l + e l) * r l + e l * x l) : ∀ l, 0 ≤ r l := by
  intro l
  induction l with
  | zero => rw [hr0]
  | succ l ih =>
    rw [hr l]
    exact add_nonneg (mul_nonneg (add_nonneg (hw l) (he l)) ih) (mul_nonneg (he l) (hx l))



theorem margin_certificate_upto (L : ℕ) (w e x r dev : ℕ → ℝ)
    (hw : ∀ l, 0 ≤ w l) (he : ∀ l, 0 ≤ e l)
    (hr0 : r 0 = 0) (hr : ∀ l, r (l+1) = (w l + e l) * r l + e l * x l)
    (hd0 : dev 0 = 0)
    (hstep : ∀ l, l < L → dev l ≤ r l → dev (l+1) ≤ w l * dev l + e l * (x l + dev l)) :
    ∀ l, l ≤ L → dev l ≤ r l := by
  intro l
  induction l with
  | zero => intro _; rw [hd0, hr0]
  | succ l ih =>
    intro hl
    have hlt : l < L := hl
    have hdl : dev l ≤ r l := ih (Nat.le_of_lt hlt)
    have h1 := hstep l hlt hdl
    have h2 : (w l + e l) * dev l ≤ (w l + e l) * r l :=
      mul_le_mul_of_nonneg_left hdl (add_nonneg (hw l) (he l))
    rw [hr l]
    nlinarith


theorem margin_certificate (w e x r dev : ℕ → ℝ)
    (hw : ∀ l, 0 ≤ w l) (he : ∀ l, 0 ≤ e l)
    (hr0 : r 0 = 0) (hr : ∀ l, r (l+1) = (w l + e l) * r l + e l * x l)
    (hd0 : dev 0 = 0)
    (hstep : ∀ l, dev l ≤ r l → dev (l+1) ≤ w l * dev l + e l * (x l + dev l)) :
    ∀ l, dev l ≤ r l := fun l =>
  margin_certificate_upto l w e x r dev hw he hr0 hr hd0 (fun k _ h => hstep k h) l le_rfl



section Matrix
open scoped Matrix.Norms.Frobenius
variable {m n N : Type*} [Fintype m] [Fintype n] [Fintype N] [DecidableEq N]


theorem frob_sq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : ‖A‖^2 = fSq A := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2:ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
  simp only [fSq, Real.rpow_two, Real.norm_eq_abs, sq_abs]

theorem fSq_sub_smul {ι κ : Type*} [Fintype ι] [Fintype κ] (A S : Matrix ι κ ℝ) (a : ℝ) :
    fSq (A - a • S) = fSq A - 2*a*fInner A S + a^2 * fSq S := by
  have h : (∑ i, ∑ j, (A i j - a * S i j)^2) =
      ∑ i, ∑ j, ((A i j)^2 - 2*a*(A i j * S i j) + a^2*(S i j)^2) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [fSq, fInner, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] using h


theorem contraction_sq (A : Matrix n N ℝ) (P : Matrix N N ℝ)
    (hs : P.transpose = P) (hp : P * P = P) (a : ℝ) :
    fSq (A * (1 - a • P)) = fSq A - a*(2-a)*fSq (A * P) := by
  have hA : A * (1 - a • P) = A - a • (A * P) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  rw [hA, fSq_sub_smul, projection_inner A P hs hp]
  ring

theorem contraction_norm_sq (A : Matrix n N ℝ) (P : Matrix N N ℝ)
    (hs : P.transpose = P) (hp : P * P = P) (a : ℝ) :
    ‖A * (1 - a • P)‖^2 = ‖A‖^2 - a*(2-a)*‖A * P‖^2 := by
  rw [frob_sq, frob_sq, frob_sq, contraction_sq A P hs hp a]


theorem contraction_norm (A : Matrix n N ℝ) (P : Matrix N N ℝ)
    (hs : P.transpose = P) (hp : P * P = P) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    ‖A * (1 - a • P)‖ ≤ ‖A‖ := by
  have h := contraction_norm_sq A P hs hp a
  have hnn : 0 ≤ a*(2-a)*‖A * P‖^2 :=
    mul_nonneg (mul_nonneg ha0 (by linarith)) (sq_nonneg _)
  have hsq : ‖A * (1 - a • P)‖^2 ≤ ‖A‖^2 := by linarith
  exact le_of_sq_le_sq hsq (norm_nonneg _)



theorem qep_pre_diff (W E : Matrix m n ℝ) (X Z : Matrix n N ℝ) (C : Matrix N n ℝ) (a : ℝ) :
    (W + a • (W * (X - Z) * C) + E) * Z - W * X
      = W * ((Z - X) * (1 - a • (C * Z))) + E * Z := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc, smul_sub]
  abel


theorem one_step_qep (W E : Matrix m n ℝ) (X Z : Matrix n N ℝ) (P : Matrix N N ℝ)
    (hs : P.transpose = P) (hp : P * P = P) (a w e : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : 0 ≤ w) (he : 0 ≤ e)
    (hW : ∀ A : Matrix n N ℝ, ‖W * A‖ ≤ w * ‖A‖)
    (hE : ∀ A : Matrix n N ℝ, ‖E * A‖ ≤ e * ‖A‖) :
    ‖W * ((Z - X) * (1 - a • P)) + E * Z‖ ≤ w * ‖Z - X‖ + e * (‖X‖ + ‖Z - X‖) := by
  have hc := contraction_norm (Z - X) P hs hp a ha0 (by linarith)
  have hZ : ‖Z‖ ≤ ‖X‖ + ‖Z - X‖ := by
    have := norm_add_le X (Z - X)
    rwa [add_sub_cancel] at this
  calc ‖W * ((Z - X) * (1 - a • P)) + E * Z‖
      ≤ ‖W * ((Z - X) * (1 - a • P))‖ + ‖E * Z‖ := norm_add_le _ _
    _ ≤ w * ‖(Z - X) * (1 - a • P)‖ + e * ‖Z‖ := add_le_add (hW _) (hE _)
    _ ≤ w * ‖Z - X‖ + e * (‖X‖ + ‖Z - X‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hc hw) (mul_le_mul_of_nonneg_left hZ he)


theorem one_step_base (W E : Matrix m n ℝ) (X Z : Matrix n N ℝ) (w e : ℝ)
    (he : 0 ≤ e)
    (hW : ∀ A : Matrix n N ℝ, ‖W * A‖ ≤ w * ‖A‖)
    (hE : ∀ A : Matrix n N ℝ, ‖E * A‖ ≤ e * ‖A‖) :
    ‖W * (Z - X) + E * Z‖ ≤ w * ‖Z - X‖ + e * (‖X‖ + ‖Z - X‖) := by
  have hZ : ‖Z‖ ≤ ‖X‖ + ‖Z - X‖ := by
    have := norm_add_le X (Z - X)
    rwa [add_sub_cancel] at this
  calc ‖W * (Z - X) + E * Z‖ ≤ ‖W * (Z - X)‖ + ‖E * Z‖ := norm_add_le _ _
    _ ≤ w * ‖Z - X‖ + e * ‖Z‖ := add_le_add (hW _) (hE _)
    _ ≤ w * ‖Z - X‖ + e * (‖X‖ + ‖Z - X‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hZ he)


theorem base_pre_diff (W E : Matrix m n ℝ) (X Z : Matrix n N ℝ) :
    (W + E) * Z - W * X = W * (Z - X) + E * Z := by
  rw [Matrix.add_mul, Matrix.mul_sub]; abel

end Matrix
end
end QepMargin
