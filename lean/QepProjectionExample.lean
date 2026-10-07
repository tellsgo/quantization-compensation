import QepCorrected


set_option autoImplicit false
namespace QepProjectionExample
noncomputable section
open QepCorrected
open scoped Matrix

def x : Mat (Fin 1) (Fin 2) := !![2, 1]
def xhat : Mat (Fin 1) (Fin 2) := !![1, 0]
def w : Mat (Fin 1) (Fin 1) := !![1]
def e : Mat (Fin 1) (Fin 1) := !![1]
def h : Mat (Fin 1) (Fin 1) := xhat * xhat.transpose
def p : Mat (Fin 2) (Fin 2) := xhat.transpose * h⁻¹ * xhat
def a : Mat (Fin 1) (Fin 2) := w * (x-xhat)
def b : Mat (Fin 1) (Fin 2) := e * xhat
def wstar : Mat (Fin 1) (Fin 1) := w + w*(x-xhat)*xhat.transpose*h⁻¹

theorem gram_is_one : h = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [h,xhat,Matrix.mul_apply,Fin.sum_univ_succ]

theorem projector_explicit : p = !![1,0;0,0] := by
  unfold p
  rw [gram_is_one]
  norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xhat,Matrix.mul_apply,Fin.sum_univ_succ]

theorem projector_not_identity : p ≠ 1 := by
  intro he
  have hh := congrArg (fun M : Mat (Fin 2) (Fin 2) => M 1 1) he
  rw [projector_explicit] at hh
  norm_num at hh

theorem actual_target : wstar = !![2] := by
  unfold wstar
  rw [gram_is_one]
  norm_num
  ext i j
  fin_cases i
  fin_cases j
  norm_num [w,x,xhat,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem actual_residuals :
    w*x-(w+e)*xhat = !![0,1] ∧
    w*x-(wstar+e)*xhat = !![-1,1] := by
  rw [actual_target]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [w,e,x,xhat,Matrix.mul_apply,Fin.sum_univ_succ]

theorem squared_residuals :
    fSq (w*x-(w+e)*xhat) = 1 ∧
    fSq (w*x-(wstar+e)*xhat) = 2 := by
  rw [actual_residuals.1,actual_residuals.2]
  norm_num [fSq,Fin.sum_univ_succ]

theorem core : h = 1 ∧ p ≠ 1 ∧
    fSq (w*x-(w+e)*xhat) = 1 ∧ fSq (w*x-(wstar+e)*xhat) = 2 :=
  ⟨gram_is_one,projector_not_identity,squared_residuals⟩

end
end QepProjectionExample
