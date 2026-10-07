import Mathlib




set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
namespace QepMatrixFamily
noncomputable section
open scoped BigOperators Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
abbrev Mat (ι κ : Type*) := Matrix ι κ ℝ
def fSq (A : Mat ι κ) : ℝ := ∑ i, ∑ j, (A i j)^2
def fro (A : Mat ι κ) : ℝ := Real.sqrt (fSq A)
def gram (X : Mat ι κ) : Mat ι ι := X * X.transpose
def z (X : Mat ι κ) (e : ℝ) : Mat ι κ := (1+e) • X
def q1 (e : ℝ) : Mat ι ι := (1:Mat ι ι) + e • 1
def b2 (e : ℝ) : Mat ι ι := (1:Mat ι ι) - e • 1
def target2 (X : Mat ι κ) (e : ℝ) : Mat ι ι :=
  1 + (X-z X e) * (z X e).transpose * (gram (z X e))⁻¹
def q2 (X : Mat ι κ) (e : ℝ) : Mat ι ι := target2 X e - e • 1
def r1 (X : Mat ι κ) (e : ℝ) : Mat ι κ := X - q1 (ι:=ι) e * X
def rb2 (X : Mat ι κ) (e : ℝ) : Mat ι κ := X - b2 (ι:=ι) e * z X e
def rq2 (X : Mat ι κ) (e : ℝ) : Mat ι κ := X - q2 X e * z X e

def baseU (X : Mat ι κ) (e : ℝ) : ℝ := fro (r1 X e) + fro (rb2 X e)
def qepU (X : Mat ι κ) (e : ℝ) : ℝ := fro (r1 X e) + fro (rq2 X e)
def projector (X : Mat ι κ) : Mat κ κ := X.transpose * (gram X)⁻¹ * X

theorem fSq_nonneg (A : Mat ι κ) : 0 ≤ fSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem fSq_smul (A : Mat ι κ) (c : ℝ) : fSq (c • A) = c^2 * fSq A := by
  simp only [fSq, Matrix.smul_apply, smul_eq_mul, mul_pow,
    Finset.mul_sum]

theorem fro_smul (A : Mat ι κ) (c : ℝ) : fro (c • A) = |c| * fro A := by
  rw [fro, fSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rfl

theorem gram_z (X : Mat ι κ) (e : ℝ) :
    gram (z X e) = (1+e)^2 • gram X := by
  simp [gram,z,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_two]

theorem gram_z_inverse (X : Mat ι κ) {e : ℝ} (he : 1+e ≠ 0)
    (hX : IsUnit (gram X).det) :
    (gram (z X e))⁻¹ = (1/(1+e)^2) • (gram X)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [gram_z,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.mul_nonsing_inv (gram X) hX]
  have hc : (1+e)^2 * (1/(1+e)^2) = 1 := by field_simp
  rw [hc,one_smul]

theorem gram_z_unit (X : Mat ι κ) {e : ℝ} (he : 1+e ≠ 0)
    (hX : IsUnit (gram X).det) : IsUnit (gram (z X e)).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := (1/(1+e)^2) • (gram X)⁻¹)
  rw [gram_z,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.mul_nonsing_inv (gram X) hX]
  have hc : (1+e)^2 * (1/(1+e)^2) = 1 := by field_simp
  rw [hc,one_smul]

theorem target2_closed (X : Mat ι κ) {e : ℝ} (he : 1+e ≠ 0)
    (hX : IsUnit (gram X).det) : target2 X e = (1/(1+e)) • (1:Mat ι ι) := by
  have hdiff : X-z X e = (-e/(1+e)) • z X e := by
    ext i j
    simp only [z,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    field_simp
    <;> ring
  unfold target2
  rw [hdiff,Matrix.smul_mul,Matrix.smul_mul]
  change 1 + (-e/(1+e)) • (gram (z X e) * (gram (z X e))⁻¹) = _
  rw [Matrix.mul_nonsing_inv _ (gram_z_unit X he hX)]
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  <;> ring

theorem residuals_closed (X : Mat ι κ) {e : ℝ} (he : 1+e ≠ 0)
    (hX : IsUnit (gram X).det) :
    r1 X e = (-e) • X ∧ rb2 X e = e^2 • X ∧ rq2 X e = (e+e^2) • X := by
  have hq := target2_closed X he hX
  constructor
  · unfold r1 q1
    rw [Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.one_mul]
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  constructor
  · unfold rb2 b2
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.one_mul]
    ext i j
    simp only [z,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  · unfold rq2 q2
    rw [hq]
    ext i j
    simp only [z,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    field_simp
    <;> ring

theorem exact_bounds (X : Mat ι κ) {e : ℝ} (he : 0<e)
    (hX : IsUnit (gram X).det) :
    baseU X e = (e+e^2)*fro X ∧ qepU X e = (2*e+e^2)*fro X := by
  have hn : 1+e ≠ 0 := by linarith
  obtain ⟨hr,hb,hq⟩ := residuals_closed X hn hX
  have hp : 0≤e+e^2 := by positivity
  constructor
  · rw [baseU,hr,hb,fro_smul,fro_smul,abs_neg,abs_of_pos he,abs_of_nonneg (sq_nonneg e)]
    ring
  · rw [qepU,hr,hq,fro_smul,fro_smul,abs_neg,abs_of_pos he,abs_of_nonneg hp]
    ring

theorem exact_gap (X : Mat ι κ) {e : ℝ} (he : 0<e)
    (hX : IsUnit (gram X).det) : qepU X e - baseU X e = e*fro X := by
  obtain ⟨hb,hq⟩ := exact_bounds X he hX
  rw [hb,hq]
  ring

theorem strict_order (X : Mat ι κ) {e : ℝ} (he : 0<e)
    (hX : IsUnit (gram X).det) (hn : 0<fSq X) : baseU X e < qepU X e := by
  have hgap := exact_gap X he hX
  have hp : 0<e*fro X := mul_pos he (Real.sqrt_pos.2 hn)
  linarith

theorem first_order_gap (X : Mat ι κ) {e : ℝ} (he : 0<e)
    (hX : IsUnit (gram X).det) : (qepU X e - baseU X e)/e = fro X := by
  rw [exact_gap X he hX]
  field_simp


def X23 : Mat (Fin 2) (Fin 3) := !![1,0,1;0,1,1]
def G23inv : Mat (Fin 2) (Fin 2) := !![2/3,-1/3;-1/3,2/3]

theorem X23_gram_inverse_certificate : gram X23 * G23inv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram,X23,G23inv,Matrix.mul_apply,Matrix.transpose_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem X23_gram_unit : IsUnit (gram X23).det :=
  Matrix.isUnit_det_of_right_inverse X23_gram_inverse_certificate

theorem X23_projector : projector X23 = !![2/3,-1/3,1/3;-1/3,2/3,1/3;1/3,1/3,2/3] := by
  have hg : (gram X23)⁻¹ = G23inv := Matrix.inv_eq_right_inv X23_gram_inverse_certificate
  unfold projector
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X23,G23inv,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]

theorem X23_projector_nonidentity : projector X23 ≠ 1 := by
  intro h
  have hh := congrArg (fun M : Mat (Fin 3) (Fin 3) => M 2 2) h
  rw [X23_projector] at hh
  norm_num at hh

theorem X23_norm : fSq X23 = 4 ∧ fro X23 = 2 := by
  constructor
  · norm_num [fSq,X23,Fin.sum_univ_succ]
  · norm_num [fro,fSq,X23,Fin.sum_univ_succ]

theorem X23_core {e : ℝ} (he : 0<e) :
    IsUnit (gram X23).det ∧ projector X23 ≠ 1 ∧
    qepU X23 e-baseU X23 e = 2*e ∧ baseU X23 e < qepU X23 e := by
  refine ⟨X23_gram_unit,X23_projector_nonidentity,?_,strict_order X23 he X23_gram_unit ?_⟩
  · rw [exact_gap X23 he X23_gram_unit,X23_norm.2]
    ring
  · rw [X23_norm.1]
    norm_num

theorem first_target_is_teacher (X : Mat ι κ) :
    (1:Mat ι ι) + (X-X)*X.transpose*(gram X)⁻¹ = 1 := by simp

theorem identity_lipschitz (A B : Mat ι κ) :
    fro ((1:Mat ι ι)*A-(1:Mat ι ι)*B) = 1*fro (A-B) := by simp

theorem scalar_identity_unit {c : ℝ} (hc : c≠0) :
    IsUnit (((c • (1:Mat ι ι))).det) := by
  rw [Matrix.det_smul,Matrix.det_one,mul_one]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc)

theorem legal_weights (X : Mat ι κ) {e : ℝ} (he : 0<e) (hu : e<1/2)
    (hX : IsUnit (gram X).det) :
    IsUnit (q1 (ι:=ι) e).det ∧ IsUnit (b2 (ι:=ι) e).det ∧ IsUnit (q2 X e).det := by
  have hp : 0<1+e := by linarith
  have hn : 1+e ≠ 0 := ne_of_gt hp
  have hq : 0<1/(1+e)-e := by
    have hs : e^2<1/4 := by nlinarith
    have hh : e*(1+e)<1 := by nlinarith
    have hd : e<1/(1+e) := (lt_div_iff₀ hp).mpr hh
    linarith
  have h1 : q1 (ι:=ι) e = (1+e) • (1:Mat ι ι) := by
    ext i j
    simp only [q1,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have hb : b2 (ι:=ι) e = (1-e) • (1:Mat ι ι) := by
    ext i j
    simp only [b2,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have h2 : q2 X e = (1/(1+e)-e) • (1:Mat ι ι) := by
    rw [q2,target2_closed X hn hX]
    ext i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [h1,hb,h2]
  exact ⟨scalar_identity_unit hn,scalar_identity_unit (by linarith),scalar_identity_unit (ne_of_gt hq)⟩

theorem projector_z (X : Mat ι κ) {e : ℝ} (he : 1+e ≠ 0)
    (hX : IsUnit (gram X).det) : projector (z X e) = projector X := by
  unfold projector
  rw [gram_z_inverse X he hX]
  simp only [z,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hc : (1+e)*(1/(1+e)^2*(1+e)) = 1 := by field_simp
  rw [hc,one_smul]

theorem first_layer_output (X : Mat ι κ) (e : ℝ) : q1 (ι:=ι) e * X = z X e := by
  unfold q1 z
  rw [Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.one_mul]
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem X23_legal_counterexample {e : ℝ} (he : 0<e) (hu : e<1/2) :
    IsUnit (gram X23).det ∧ IsUnit (gram (z X23 e)).det ∧
    IsUnit (q1 (ι:=Fin 2) e).det ∧ IsUnit (b2 (ι:=Fin 2) e).det ∧ IsUnit (q2 X23 e).det ∧
    projector (z X23 e) ≠ 1 ∧ qepU X23 e-baseU X23 e=2*e ∧ baseU X23 e<qepU X23 e := by
  have hn : 1+e ≠ 0 := by linarith
  obtain ⟨h1,hb,hq⟩ := legal_weights X23 he hu X23_gram_unit
  refine ⟨X23_gram_unit,gram_z_unit X23 hn X23_gram_unit,h1,hb,hq,?_,(X23_core he).2.2.1,(X23_core he).2.2.2⟩
  rw [projector_z X23 hn X23_gram_unit]
  exact X23_projector_nonidentity

end
end QepMatrixFamily
