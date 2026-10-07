import QepFiniteDitherMatrix
set_option maxHeartbeats 1400000
set_option linter.unusedVariables false
open QepFiniteDitherLaw QepFiniteDitherMatrix
namespace QepFiniteOverloadExamples
noncomputable section


def correction (W X Z : Mat) : Mat := W*(X-Z)*Z.transpose*(Z*Z.transpose)⁻¹
def target (W X Z : Mat) (α : ℝ) : Mat := W+α • correction W X Z

def T : Mat := !![(4:ℝ),1;0,1]
def W₁ : Mat := !![(4:ℝ),2;0,1]
def Z₁ : Mat := !![(1:ℝ),0;1,1/2]
def X₁ : Mat := !![(3/4:ℝ),-1/8;1,1/2]
def W₂ : Mat := !![(2:ℝ),2;0,1]
def Z₂ : Mat := !![(1:ℝ),0;2,1/2]
def X₂ : Mat := !![(1:ℝ),-1/4;2,1/2]

theorem example1_invertible_inputs : W₁.det=4 ∧ Z₁.det=1/2 ∧ X₁.det=1/2 := by
  norm_num [W₁,Z₁,X₁,Matrix.det_fin_two]
theorem example2_invertible_inputs : W₂.det=2 ∧ Z₂.det=1/2 ∧ X₂.det=1 := by
  norm_num [W₂,Z₂,X₂,Matrix.det_fin_two]

theorem example1_teacher : W₁*X₁=T*Z₁ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [W₁,X₁,T,Z₁,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
theorem example2_teacher : W₂*X₂=T*Z₂ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [W₂,X₂,T,Z₂,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem example1_inverse_weight : W₁⁻¹=!![(1/4:ℝ),-1/2;0,1] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [W₁,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
theorem example2_inverse_weight : W₂⁻¹=!![(1/2:ℝ),-1;0,1] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [W₂,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
theorem example1_constructed_input : X₁=W₁⁻¹*T*Z₁ := by
  rw [example1_inverse_weight]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [X₁,T,Z₁,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
theorem example2_constructed_input : X₂=W₂⁻¹*T*Z₂ := by
  rw [example2_inverse_weight]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [X₂,T,Z₂,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem example1_gram_inverse : (Z₁*Z₁.transpose)⁻¹=!![(5:ℝ),-4;-4,4] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Z₁,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
theorem example2_gram_inverse : (Z₂*Z₂.transpose)⁻¹=!![(17:ℝ),-8;-8,4] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Z₂,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem example1_projection : Z₁.transpose*(Z₁*Z₁.transpose)⁻¹*Z₁=1 := by
  rw [example1_gram_inverse]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Z₁,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
theorem example2_projection : Z₂.transpose*(Z₂*Z₂.transpose)⁻¹*Z₂=1 := by
  rw [example2_gram_inverse]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Z₂,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem example1_correction : correction W₁ X₁ Z₁=!![(0:ℝ),-1;0,0] := by
  unfold correction
  rw [example1_gram_inverse]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [W₁,X₁,Z₁,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
theorem example2_correction : correction W₂ X₂ Z₂=!![(2:ℝ),-1;0,0] := by
  unfold correction
  rw [example2_gram_inverse]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [W₂,X₂,Z₂,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem example1_target (α : ℝ) : target W₁ X₁ Z₁ α=!![(4:ℝ),2-α;0,1] := by
  rw [target,example1_correction]
  ext i j; fin_cases i <;> fin_cases j <;> simp [W₁] <;> ring
theorem example2_target (α : ℝ) : target W₂ X₂ Z₂ α=!![(2+2*α:ℝ),2-α;0,1] := by
  rw [target,example2_correction]
  ext i j; fin_cases i <;> fin_cases j <;> simp [W₂] <;> ring


def F₁ (α : ℝ) := expectedLoss 3 (W₁*X₁) (target W₁ X₁ Z₁ α) Z₁
def F₂ (α : ℝ) := expectedLoss 3 (W₂*X₂) (target W₂ X₂ Z₂ α) Z₂

theorem clip_two_sub (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : clip 3 (2-α)=2-α := by
  norm_num [clip,min_eq_right (show 2-α≤(3:ℝ) by linarith),max_eq_right (show 0≤2-α by linarith)]

theorem example1_actual_expected_loss (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    F₁ α=5/8-α/2+5/4*α^2 := by
  rw [F₁,example1_teacher,example1_target,expectedLoss_formula]
  have hc := clip_two_sub α h0 h1
  norm_num [T,Z₁,fSq,clipped,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,clip] at hc ⊢
  rw [hc]
  ring

theorem example1_endpoints : F₁ 0=5/8 ∧ F₁ 1=11/8 ∧ F₁ 1-F₁ 0=3/4 := by
  have h0 := example1_actual_expected_loss 0 (by norm_num) (by norm_num)
  have h1 := example1_actual_expected_loss 1 (by norm_num) (by norm_num)
  norm_num at h0 h1
  exact ⟨h0,h1,by rw [h0,h1]; norm_num⟩

theorem example1_minimum (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    F₁ α-F₁ (1/5)=5/4*(α-1/5)^2 ∧ F₁ (1/5)≤F₁ α := by
  rw [example1_actual_expected_loss α h0 h1,
    example1_actual_expected_loss (1/5) (by norm_num) (by norm_num)]
  constructor
  · ring
  · nlinarith [sq_nonneg (α-1/5)]

theorem clip_two_add (α : ℝ) (h0 : 0 ≤ α) :
    clip 3 (2+2*α)=2+2*α-max 0 (2*α-1) := by
  by_cases h : 2*α≤1
  · rw [max_eq_left (by linarith : 2*α-1≤0)]
    norm_num [clip,min_eq_right (show 2+2*α≤(3:ℝ) by linarith),max_eq_right (show 0≤2+2*α by linarith)]
  · rw [max_eq_right (by linarith : 0≤2*α-1)]
    norm_num [clip,min_eq_left (show (3:ℝ)≤2+2*α by linarith)]
    ring

theorem example2_actual_expected_loss (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    F₂ α=7/8+(1-α)^2/4+(max 0 (2*α-1))^2 := by
  rw [F₂,example2_teacher,example2_target,expectedLoss_formula]
  have hc := clip_two_sub α h0 h1
  have hd := clip_two_add α h0
  norm_num [T,Z₂,fSq,clipped,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,clip] at hc hd ⊢
  rw [hc,hd]
  ring

theorem example2_endpoints : F₂ 0=9/8 ∧ F₂ 1=15/8 ∧ F₂ 1-F₂ 0=3/4 := by
  have h0 := example2_actual_expected_loss 0 (by norm_num) (by norm_num)
  have h1 := example2_actual_expected_loss 1 (by norm_num) (by norm_num)
  norm_num at h0 h1
  exact ⟨h0,h1,by rw [h0,h1]; norm_num⟩

theorem example2_base_no_overload (i j : Fin 2) : 0≤W₂ i j ∧ W₂ i j≤3 := by
  fin_cases i <;> fin_cases j <;> norm_num [W₂]
theorem example2_propagated_overload (α : ℝ) :
    3 < target W₂ X₂ Z₂ α 0 0 ↔ 1/2 < α := by
  rw [example2_target]; simp; constructor <;> intro h <;> linarith
end
end QepFiniteOverloadExamples
