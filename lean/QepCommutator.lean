import QepLinearOrder






set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QepComm
noncomputable section
open Matrix QepCorrected QepLinear

variable {d n : Type*} [Fintype d] [Fintype n] [DecidableEq d] [DecidableEq n]



def BilBound (B : Mat n n) (k : ℝ) : Prop :=
  ∀ x y : n → ℝ, |x ⬝ᵥ (B *ᵥ y)| ≤ k * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)

theorem dp_self_nonneg (x : n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))


theorem BilBound.nonneg_of_ne {B : Mat n n} {k : ℝ} (h : BilBound B k)
    (x : n → ℝ) (hx : x ⬝ᵥ x ≠ 0) : 0 ≤ k := by
  have hs : 0 < Real.sqrt (x ⬝ᵥ x) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne (dp_self_nonneg x) (Ne.symm hx))
  have h1 := (abs_nonneg _).trans (h x x)
  by_contra hk
  have hk := not_le.mp hk
  nlinarith [mul_pos (neg_pos.mpr hk) (mul_pos hs hs)]


theorem bil_factor (P B Q : Mat n n) (hs : Pᵀ = P) (x y : n → ℝ) :
    x ⬝ᵥ ((P * B * Q) *ᵥ y) = (P *ᵥ x) ⬝ᵥ (B *ᵥ (Q *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hs]

theorem proj_self (P : Mat n n) (hs : Pᵀ = P) (hp : P * P = P) (x : n → ℝ) :
    (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ x) := by
  have h := bil_factor P 1 P hs x x
  rw [Matrix.mul_one, hp, Matrix.one_mulVec] at h
  exact h.symm

theorem compl_symm (P : Mat n n) (hs : Pᵀ = P) : (1 - P)ᵀ = 1 - P := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, hs]

theorem compl_idem (P : Mat n n) (hp : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hp]
  abel


theorem pyth (P : Mat n n) (hs : Pᵀ = P) (hp : P * P = P) (x : n → ℝ) :
    (P *ᵥ x) ⬝ᵥ (P *ᵥ x) + ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) = x ⬝ᵥ x := by
  rw [proj_self P hs hp, proj_self (1 - P) (compl_symm P hs) (compl_idem P hp),
    ← dotProduct_add, ← Matrix.add_mulVec]
  simp


theorem comm_compress_eq (P J : Mat n n) (hp : P * P = P) :
    P * (P * J - J * P) * (1 - P) = P * J * (1 - P) := by
  have hp' : ∀ M : Mat n n, P * (P * M) = P * M := fun M => by
    rw [← Matrix.mul_assoc, hp]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, hp, hp']
  abel


theorem BilBound.compress {C : Mat n n} {k : ℝ} (hC : BilBound C k)
    (P : Mat n n) (hs : Pᵀ = P) (hp : P * P = P) : BilBound (P * C * (1 - P)) k := by
  intro x y
  rw [bil_factor P C (1 - P) hs]
  have h := hC (P *ᵥ x) ((1 - P) *ᵥ y)
  by_cases hx : x ⬝ᵥ x = 0
  · have hx0 : x = 0 := dotProduct_self_eq_zero.mp hx
    subst hx0
    simp
  · have hk0 := hC.nonneg_of_ne x hx
    have h1 : Real.sqrt ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) ≤ Real.sqrt (x ⬝ᵥ x) := by
      apply Real.sqrt_le_sqrt
      have := pyth P hs hp x
      have := dp_self_nonneg ((1 - P) *ᵥ x)
      linarith
    have h2 : Real.sqrt (((1 - P) *ᵥ y) ⬝ᵥ ((1 - P) *ᵥ y)) ≤ Real.sqrt (y ⬝ᵥ y) := by
      apply Real.sqrt_le_sqrt
      have := pyth P hs hp y
      have := dp_self_nonneg (P *ᵥ y)
      linarith
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 hk0) h2 (Real.sqrt_nonneg _)
      (mul_nonneg hk0 (Real.sqrt_nonneg _)))


theorem BilBound.of_commutator {P J : Mat n n} {k : ℝ} (hs : Pᵀ = P) (hp : P * P = P)
    (hC : BilBound (P * J - J * P) k) : BilBound (P * J * (1 - P)) k := by
  have h := hC.compress P hs hp
  rwa [comm_compress_eq P J hp] at h


theorem cross_posSemidef (P B : Mat n n) (hs : Pᵀ = P) (hp : P * P = P)
    (hB : P * B * (1 - P) = B) (k : ℝ) (hk : BilBound B k) :
    (B + Bᵀ + k • (1 : Mat n n)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.transpose_one]
    abel
  · intro x
    have e1 : x ⬝ᵥ (Bᵀ *ᵥ x) = x ⬝ᵥ (B *ᵥ x) := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    have e2 : x ⬝ᵥ (B *ᵥ x) = (P *ᵥ x) ⬝ᵥ (B *ᵥ ((1 - P) *ᵥ x)) := by
      rw [← bil_factor P B (1 - P) hs, hB]
    have hb := hk (P *ᵥ x) ((1 - P) *ᵥ x)
    have hpy := pyth P hs hp x
    have hpn := dp_self_nonneg (P *ᵥ x)
    have hqn := dp_self_nonneg ((1 - P) *ᵥ x)
    have hs2 := Real.sq_sqrt hpn
    have ht2 := Real.sq_sqrt hqn
    have hsn := Real.sqrt_nonneg ((P *ᵥ x) ⬝ᵥ (P *ᵥ x))
    have htn := Real.sqrt_nonneg (((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x))
    rw [star_trivial, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
      e1, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, e2]
    have hab := neg_abs_le ((P *ᵥ x) ⬝ᵥ (B *ᵥ ((1 - P) *ᵥ x)))
    by_cases hx : x ⬝ᵥ x = 0
    · have h1 : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = 0 := by linarith
      rw [h1, Real.sqrt_zero] at hb
      rw [hx]
      simp only [mul_zero, zero_mul] at hb
      linarith
    · have hk0 := hk.nonneg_of_ne x hx
      nlinarith [mul_nonneg hk0 (sq_nonneg (Real.sqrt ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) -
        Real.sqrt (((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x))))]

theorem B_fix (P J : Mat n n) (hp : P * P = P) :
    P * (P * J * (1 - P)) * (1 - P) = P * J * (1 - P) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hp, Matrix.mul_assoc, compl_idem P hp]

theorem B_transpose (P J : Mat n n) (hs : Pᵀ = P) (hJs : Jᵀ = J) :
    (P * J * (1 - P))ᵀ = (1 - P) * J * P := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, compl_symm P hs, hs, hJs, Matrix.mul_assoc]

theorem proj_posSemidef (J : Mat n n) (hJs : Jᵀ = J) (hJ : J * J = J) : J.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose J
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hJs, hJ] at h

theorem sandwich_posSemidef {M : Mat n n} (h : M.PosSemidef) (W : Mat d n) :
    (W * M * Wᵀ).PosSemidef := by
  have h' := h.mul_mul_conjTranspose_same W
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h'


theorem T1_decomp (P J : Mat n n) (a k : ℝ) :
    J + (a * k) • (1 : Mat n n) - (1 - a • P) * J * (1 - a • P) =
      (a * (2 - a)) • (P * J * P) +
        a • (P * J * (1 - P) + (1 - P) * J * P + k • (1 : Mat n n)) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  module


theorem T2_decomp (P J : Mat n n) (k : ℝ) :
    J + k • (1 : Mat n n) - P * J * P =
      (1 - P) * J * (1 - P) + (P * J * (1 - P) + (1 - P) * J * P + k • (1 : Mat n n)) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  abel


theorem T1_core (P J : Mat n n) (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J.PosSemidef) (a : ℝ) (h0 : 0 ≤ a) (h2 : a ≤ 2)
    (k : ℝ) (hk : BilBound (P * J * (1 - P)) k) :
    (J + (a * k) • (1 : Mat n n) - (1 - a • P) * J * (1 - a • P)).PosSemidef := by
  rw [T1_decomp]
  have hc := cross_posSemidef P (P * J * (1 - P)) hs hp (B_fix P J hp) k hk
  rw [B_transpose P J hs hJs] at hc
  have hPJP : (P * J * P).PosSemidef := by
    have h := sandwich_posSemidef hJ P
    rwa [hs] at h
  exact (hPJP.smul (mul_nonneg h0 (by linarith))).add (hc.smul h0)


theorem T2_core (P J : Mat n n) (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J.PosSemidef)
    (k : ℝ) (hk : BilBound (P * J * (1 - P)) k) :
    (J + k • (1 : Mat n n) - P * J * P).PosSemidef := by
  rw [T2_decomp]
  have hc := cross_posSemidef P (P * J * (1 - P)) hs hp (B_fix P J hp) k hk
  rw [B_transpose P J hs hJs] at hc
  have hQ : ((1 - P) * J * (1 - P)).PosSemidef := by
    have h := sandwich_posSemidef hJ (1 - P)
    rwa [compl_symm P hs] at h
  exact hQ.add hc


theorem T1_proj (P J : Mat n n) (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J * J = J) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (k : ℝ) (hk : BilBound (P * J * (1 - P)) k) :
    (J + (a * k) • (1 : Mat n n) - (1 - a • P) * J * (1 - a • P)).PosSemidef :=
  T1_core P J hs hp hJs (proj_posSemidef J hJs hJ) a h0 (by linarith) k hk


theorem T2_proj (P J : Mat n n) (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J * J = J)
    (k : ℝ) (hk : BilBound (P * J * (1 - P)) k) :
    (J + k • (1 : Mat n n) - P * J * P).PosSemidef :=
  T2_core P J hs hp hJs (proj_posSemidef J hJs hJ) k hk


theorem T1_commutator (P J : Mat n n) (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J * J = J) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (k : ℝ) (hk : BilBound (P * J - J * P) k) :
    (J + (a * k) • (1 : Mat n n) - (1 - a • P) * J * (1 - a • P)).PosSemidef :=
  T1_proj P J hs hp hJs hJ a h0 h1 k (BilBound.of_commutator hs hp hk)


theorem T2_commutator (P J : Mat n n) (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J * J = J)
    (k : ℝ) (hk : BilBound (P * J - J * P) k) :
    (J + k • (1 : Mat n n) - P * J * P).PosSemidef :=
  T2_proj P J hs hp hJs hJ k (BilBound.of_commutator hs hp hk)


theorem T3_residual (a : ℝ) (Z X : Mat d n) (P : Mat n n) (hz : Z * P = Z) :
    ((1 - a) • Z + a • (X * P)) - X = (Z - X) * (1 - a • P) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, hz]
  module

theorem sandwich_sub (R : Mat d n) (U J : Mat n n) (c : ℝ) (hU : Uᵀ = U) :
    R * J * Rᵀ + c • (R * Rᵀ) - (R * U) * J * (R * U)ᵀ =
      R * (J + c • (1 : Mat n n) - U * J * U) * Rᵀ := by
  simp only [Matrix.transpose_mul, hU, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]

theorem U_symm (a : ℝ) (P : Mat n n) (hs : Pᵀ = P) : (1 - a • P)ᵀ = 1 - a • P := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hs]


theorem T3_error (a : ℝ) (Z X : Mat d n) (P J : Mat n n)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z)
    (hJs : Jᵀ = J) (hJ : J * J = J) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (k : ℝ) (hk : BilBound (P * J * (1 - P)) k) :
    Loewner
      ((((1 - a) • Z + a • (X * P)) - X) * J * (((1 - a) • Z + a • (X * P)) - X)ᵀ)
      ((Z - X) * J * (Z - X)ᵀ + (a * k) • ((Z - X) * (Z - X)ᵀ)) := by
  unfold Loewner
  rw [T3_residual a Z X P hz, sandwich_sub (Z - X) (1 - a • P) J (a * k) (U_symm a P hs)]
  exact sandwich_posSemidef (T1_proj P J hs hp hJs hJ a h0 h1 k hk) (Z - X)


theorem T4_identity (a : ℝ) (Z Y : Mat d n) (J : Mat n n) :
    (1 - a) • (Z * J * Zᵀ) + a • (Y * J * Yᵀ)
        - ((1 - a) • Z + a • Y) * J * ((1 - a) • Z + a • Y)ᵀ =
      (a * (1 - a)) • ((Z - Y) * J * (Z - Y)ᵀ) := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul]
  module

theorem T4_split (X : Mat d n) (P J : Mat n n) (hs : Pᵀ = P) (k : ℝ) :
    X * (J + k • (1 : Mat n n) - P * J * P) * Xᵀ =
      X * J * Xᵀ + k • (X * Xᵀ) - (X * P) * J * (X * P)ᵀ := by
  simp only [Matrix.transpose_mul, hs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]


theorem T4_gram (a : ℝ) (Z X : Mat d n) (P J : Mat n n)
    (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J * J = J) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (k : ℝ) (hk : BilBound (P * J * (1 - P)) k) :
    Loewner
      (((1 - a) • Z + a • (X * P)) * J * ((1 - a) • Z + a • (X * P))ᵀ)
      ((1 - a) • (Z * J * Zᵀ) + a • (X * J * Xᵀ) + (a * k) • (X * Xᵀ)) := by
  unfold Loewner
  have hJp := proj_posSemidef J hJs hJ
  have p1 := (sandwich_posSemidef (T2_proj P J hs hp hJs hJ k hk) X).smul h0
  have p2 := (sandwich_posSemidef hJp (Z - X * P)).smul
    (mul_nonneg h0 (show (0:ℝ) ≤ 1 - a by linarith))
  rw [T4_split X P J hs k] at p1
  rw [← T4_identity a Z (X * P) J] at p2
  have e : a • (X * J * Xᵀ + k • (X * Xᵀ) - X * P * J * (X * P)ᵀ) +
      ((1 - a) • (Z * J * Zᵀ) + a • (X * P * J * (X * P)ᵀ) -
        ((1 - a) • Z + a • (X * P)) * J * ((1 - a) • Z + a • (X * P))ᵀ) =
      (1 - a) • (Z * J * Zᵀ) + a • (X * J * Xᵀ) + (a * k) • (X * Xᵀ) -
        ((1 - a) • Z + a • (X * P)) * J * ((1 - a) • Z + a • (X * P))ᵀ := by
    module
  rw [← e]
  exact p1.add p2


theorem T3_error_commutator (a : ℝ) (Z X : Mat d n) (P J : Mat n n)
    (hs : Pᵀ = P) (hp : P * P = P) (hz : Z * P = Z)
    (hJs : Jᵀ = J) (hJ : J * J = J) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (k : ℝ) (hk : BilBound (P * J - J * P) k) :
    Loewner
      ((((1 - a) • Z + a • (X * P)) - X) * J * (((1 - a) • Z + a • (X * P)) - X)ᵀ)
      ((Z - X) * J * (Z - X)ᵀ + (a * k) • ((Z - X) * (Z - X)ᵀ)) :=
  T3_error a Z X P J hs hp hz hJs hJ h0 h1 k (BilBound.of_commutator hs hp hk)


theorem T4_gram_commutator (a : ℝ) (Z X : Mat d n) (P J : Mat n n)
    (hs : Pᵀ = P) (hp : P * P = P)
    (hJs : Jᵀ = J) (hJ : J * J = J) (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (k : ℝ) (hk : BilBound (P * J - J * P) k) :
    Loewner
      (((1 - a) • Z + a • (X * P)) * J * ((1 - a) • Z + a • (X * P))ᵀ)
      ((1 - a) • (Z * J * Zᵀ) + a • (X * J * Xᵀ) + (a * k) • (X * Xᵀ)) :=
  T4_gram a Z X P J hs hp hJs hJ h0 h1 k (BilBound.of_commutator hs hp hk)

end
end QepComm
