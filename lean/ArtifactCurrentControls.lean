import QepCommutator
import QepDefectKernel
open Matrix QepCorrected QepLinear QepComm
namespace ArtifactCurrentControls
noncomputable section

example {n : Type*} [Fintype n] [DecidableEq n] (P J : Mat n n)
    (hs : Pᵀ = P) (hp : P * P = P) (hJs : Jᵀ = J) (hJ : J * J = J)
    (hc : P * J - J * P = 0) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (J - (1 - a • P) * J * (1 - a • P)).PosSemidef := by
  have hb : BilBound (P * J - J * P) 0 := by
    intro x y
    simp [hc]
  simpa using T1_commutator P J hs hp hJs hJ a h0 h1 0 hb

def P : Mat (Fin 2) (Fin 2) := !![(1/2:ℝ),1/2;1/2,1/2]
def J : Mat (Fin 2) (Fin 2) := !![(1:ℝ),0;0,0]
theorem omitted_defect_witness :
    (![0,1] : Fin 2 → ℝ) ⬝ᵥ ((J - P * J * P) *ᵥ ![0,1]) = -1/4 := by
  norm_num [P,J,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
theorem relu_spectral_witness : (5:ℚ) > 2 * 2 := by norm_num
end
end ArtifactCurrentControls
