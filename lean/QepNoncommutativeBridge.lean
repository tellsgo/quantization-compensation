import QepNoncommutative
set_option maxHeartbeats 1000000
open scoped Matrix
open QepNoncommutative
namespace QepNoncommutativeBridge
noncomputable section


def spectral (A : M2) : ℝ := ‖Matrix.toEuclideanCLM (𝕜:=ℝ) A‖

theorem teacher_spectral_norm {a b : ℝ} (hb : 0<b) (hab : b≤a) : spectral (W2 a b)=a := by
  open scoped Matrix.Norms.L2Operator in
    rw [spectral,W2,Matrix.l2_opNorm_toEuclideanCLM,D_eq_diagonal,Matrix.l2_opNorm_diagonal]
  have ha : 0<a := lt_of_lt_of_le hb hab
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg ha.le).mpr
    intro i; fin_cases i <;> simp [Real.norm_eq_abs,abs_of_pos ha,abs_of_pos hb,hab]
  · have h := norm_le_pi_norm (![a,b] : Fin 2→ℝ) 0
    simpa [Real.norm_eq_abs,abs_of_pos ha] using h

def actualBU (a b t : ℝ) : ℝ := spectral (W2 a b)*fro (bR1 t)+fro (bR2 a b t)
def actualQU (a b t : ℝ) : ℝ := spectral (W2 a b)*fro (qR1 t)+fro (qR2 a b t)

theorem actual_bounds_bridge {a b t : ℝ} (hb : 0<b) (hab : 2*b<a) :
    actualBU a b t=bU a b t ∧ actualQU a b t=qU a b t := by
  simp [actualBU,actualQU,bU,qU,teacher_spectral_norm hb (by linarith)]

theorem actual_bound_gap {a b t : ℝ} (hb : 0<b) (hab : 2*b<a) (ht : 0<t) :
    actualQU a b t-actualBU a b t=(a-2*b)*t ∧ 0<(a-2*b)*t := by
  rw [(actual_bounds_bridge hb hab).1,(actual_bounds_bridge hb hab).2]
  obtain ⟨h1,h2,_⟩ := bounds hb hab ht
  rw [h1,h2]
  constructor
  · ring
  · exact mul_pos (by linarith) ht

theorem second_weights_det (a b t : ℝ) : (bQ2 a b t).det=a*b ∧ (qQ2 a b t).det=a*b := by
  rw [(second_weights a b t).1,(second_weights a b t).2]
  simp [Matrix.det_fin_two,D,N]

theorem first_weights_unit (t : ℝ) : IsUnit (bQ1 t) ∧ IsUnit (qQ1 t) := by
  rw [bQ1_eq,qQ1_eq]
  have h := Matrix.isUnit_det_of_right_inverse (second_input_inverse t).1
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr h,(Matrix.isUnit_iff_isUnit_det _).mpr h⟩

theorem second_weights_unit {a b : ℝ} (ha : a≠0) (hb : b≠0) (t : ℝ) :
    IsUnit (bQ2 a b t) ∧ IsUnit (qQ2 a b t) := by
  constructor
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [(second_weights_det a b t).1]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero ha hb)
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [(second_weights_det a b t).2]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero ha hb)

theorem both_input_grams_unit (t : ℝ) :
    IsUnit (bZ2 t*(bZ2 t)ᵀ) ∧ IsUnit (qZ2 t*(qZ2 t)ᵀ) := by
  have h : bZ2 t=qZ2 t := (second_input t).1.trans (second_input t).2.symm
  rw [h]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (gram2_unit t),(Matrix.isUnit_iff_isUnit_det _).mpr (gram2_unit t)⟩

theorem teacher_weights_unit {a b : ℝ} (ha : a≠0) (hb : b≠0) :
    IsUnit W1 ∧ IsUnit (W2 a b) := by
  constructor
  · simp [W1]
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simp only [W2,D,Matrix.det_fin_two]
    simpa using (isUnit_iff_ne_zero.mpr (mul_ne_zero ha hb) : IsUnit (a*b))

theorem teacher_input_grams_unit : IsUnit (X*Xᵀ) ∧ IsUnit (X2*X2ᵀ) := by
  simp [X,X2_eq]

theorem N_nonzero : N≠0 := by
  intro h
  have hh := congrArg (fun A : M2 => A 0 1) h
  norm_num [N] at hh

theorem no_common_similarity_diagonalization {a b : ℝ} (hab : a≠b) :
    ¬ ∃ (S : M2ˣ) (u v : Fin 2→ℝ),
      (↑S⁻¹ : M2)*N*(↑S : M2)=Matrix.diagonal u ∧
      (↑S⁻¹ : M2)*D a b*(↑S : M2)=Matrix.diagonal v := by
  rintro ⟨S,u,v,hu,hv⟩
  have hd : (Matrix.diagonal u : M2)*Matrix.diagonal v=Matrix.diagonal v*Matrix.diagonal u := by
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact mul_comm _ _
  rw [←hu,←hv] at hd
  have hh := congrArg (fun A : M2 => (↑S : M2)*A*(↑S⁻¹ : M2)) hd
  apply noncommuting hab
  simpa [Matrix.mul_assoc] using hh

theorem N_not_similarity_diagonalizable :
    ¬ ∃ (S : M2ˣ) (u : Fin 2→ℝ), (↑S⁻¹ : M2)*N*(↑S : M2)=Matrix.diagonal u := by
  rintro ⟨S,u,hu⟩
  have hs : ((↑S⁻¹ : M2)*N*(↑S : M2))*((↑S⁻¹ : M2)*N*(↑S : M2))=0 := by
    calc
      _ = (↑S⁻¹ : M2)*(N*N)*(↑S : M2) := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [N_sq]; simp
  rw [hu,Matrix.diagonal_mul_diagonal] at hs
  have hz : u=0 := by
    funext i
    have hi := congrArg (fun A : M2 => A i i) hs
    simpa using (mul_self_eq_zero.mp (by simpa using hi) : u i=0)
  have hz0 : Matrix.diagonal (0 : Fin 2→ℝ)=(0:M2) := by ext i j; simp [Matrix.diagonal]
  rw [hz,hz0] at hu
  have hh := congrArg (fun A : M2 => (↑S : M2)*A*(↑S⁻¹ : M2)) hu
  apply N_nonzero
  simpa [Matrix.mul_assoc] using hh

theorem equal_diagonal_qep_exact (b t : ℝ) : qZ3 b b t=X3 b b := by
  rw [(outputs b b t).2,X3_eq]
  simp


theorem actual_output_norms {a b t : ℝ} (hb : 0<b) (hab : 2*b<a) (ht : 0<t) :
    fro (X3 a b-bZ3 a b t)=b*t ∧ fro (X3 a b-qZ3 a b t)=(a-b)*t := by
  exact ⟨(residual_norms hb hab ht).2.2.1,(residual_norms hb hab ht).2.2.2⟩

theorem noncommuting_but_improves :
    N*D (3/2) 1 ≠ D (3/2) 1*N ∧
    fSq (X3 (3/2) 1-qZ3 (3/2) 1 1)<fSq (X3 (3/2) 1-bZ3 (3/2) 1 1) := by
  constructor
  · exact noncommuting (by norm_num)
  · rw [(output_errors (3/2) 1 1).1,(output_errors (3/2) 1 1).2]
    norm_num

end
end QepNoncommutativeBridge
