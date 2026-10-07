import QepFiniteDitherLaw

set_option maxHeartbeats 1800000
set_option linter.unusedVariables false
open MeasureTheory Set
open QepFiniteDitherLaw
namespace QepFiniteDitherMatrix
noncomputable section

abbrev Pair := ℝ × ℝ
def rowNoise : Measure Pair := noise.prod noise
instance : IsProbabilityMeasure rowNoise := inferInstanceAs (IsProbabilityMeasure (noise.prod noise))
def fourNoise : Measure (Pair × Pair) := rowNoise.prod rowNoise
instance : IsProbabilityMeasure fourNoise := inferInstanceAs (IsProbabilityMeasure (rowNoise.prod rowNoise))
def centered (k : ℕ) (t u : ℝ) := reconstruction k t u - clip k t

theorem centered_integrable (k : ℕ) (t : ℝ) : Integrable (centered k t) noise := by
  change Integrable (fun u => reconstruction k t u - clip k t) noise
  simpa only [pow_one] using centered_integrable_power k 1 t

def expanded (k : ℕ) (t s a b c : ℝ) (uv : Pair) :=
  a^2 + (2*a*b)*centered k t uv.1 + (2*a*c)*centered k s uv.2 +
    b^2*(centered k t uv.1)^2 + c^2*(centered k s uv.2)^2 +
    (2*b*c)*(centered k t uv.1*centered k s uv.2)

theorem expanded_integrable (k : ℕ) (t s a b c : ℝ) :
    Integrable (expanded k t s a b c) rowNoise := by
  have h1 := (centered_integrable k t).comp_fst noise
  have h2 := (centered_integrable k s).comp_snd noise
  have h11 : Integrable (fun uv : Pair => (centered k t uv.1)^2) rowNoise :=
    (centered_integrable_power k 2 t).comp_fst noise
  have h22 : Integrable (fun uv : Pair => (centered k s uv.2)^2) rowNoise :=
    (centered_integrable_power k 2 s).comp_snd noise
  have h12 := (centered_integrable k t).mul_prod (centered_integrable k s)
  exact (((((integrable_const (a^2)).add (h1.const_mul (2*a*b))).add
    (h2.const_mul (2*a*c))).add (h11.const_mul (b^2))).add
    (h22.const_mul (c^2))).add (h12.const_mul (2*b*c))

theorem centered_pair_square_integrable (k : ℕ) (t s a b c : ℝ) :
    Integrable (fun uv : Pair => (a+b*centered k t uv.1+c*centered k s uv.2)^2) rowNoise := by
  convert expanded_integrable k t s a b c using 1
  funext uv; dsimp [expanded]; ring

theorem centered_pair_square (k : ℕ) (t s a b c : ℝ) :
    (∫ uv : Pair, (a+b*centered k t uv.1+c*centered k s uv.2)^2 ∂rowNoise) =
      a^2+(b^2+c^2)/12 := by
  have h1 : Integrable (fun uv : Pair => centered k t uv.1) rowNoise :=
    (centered_integrable k t).comp_fst noise
  have h2 : Integrable (fun uv : Pair => centered k s uv.2) rowNoise :=
    (centered_integrable k s).comp_snd noise
  have h11 : Integrable (fun uv : Pair => (centered k t uv.1)^2) rowNoise :=
    (centered_integrable_power k 2 t).comp_fst noise
  have h22 : Integrable (fun uv : Pair => (centered k s uv.2)^2) rowNoise :=
    (centered_integrable_power k 2 s).comp_snd noise
  have h12 : Integrable (fun uv : Pair => centered k t uv.1*centered k s uv.2) rowNoise :=
    (centered_integrable k t).mul_prod (centered_integrable k s)
  have heq : (fun uv : Pair => (a+b*centered k t uv.1+c*centered k s uv.2)^2) =
      expanded k t s a b c := by funext uv; dsimp [expanded]; ring
  rw [heq]
  unfold expanded
  have ha1 : Integrable (fun uv : Pair => a^2+(2*a*b)*centered k t uv.1) rowNoise :=
    (integrable_const _).add (h1.const_mul _)
  have ha2 : Integrable (fun uv : Pair => a^2+(2*a*b)*centered k t uv.1+(2*a*c)*centered k s uv.2) rowNoise :=
    ha1.add (h2.const_mul _)
  have ha3 : Integrable (fun uv : Pair => a^2+(2*a*b)*centered k t uv.1+(2*a*c)*centered k s uv.2+b^2*(centered k t uv.1)^2) rowNoise :=
    ha2.add (h11.const_mul _)
  have ha4 : Integrable (fun uv : Pair => a^2+(2*a*b)*centered k t uv.1+(2*a*c)*centered k s uv.2+b^2*(centered k t uv.1)^2+c^2*(centered k s uv.2)^2) rowNoise :=
    ha3.add (h22.const_mul _)
  rw [integral_add ha4 (h12.const_mul _),integral_add ha3 (h22.const_mul _),
    integral_add ha2 (h11.const_mul _),integral_add ha1 (h2.const_mul _),
    integral_add (integrable_const _) (h1.const_mul _)]
  simp only [integral_const_mul]
  unfold rowNoise
  rw [integral_fun_fst (centered k t),integral_fun_snd (centered k s),
    integral_fun_fst (fun u => (centered k t u)^2),
    integral_fun_snd (fun u => (centered k s u)^2),
    integral_prod_mul (centered k t) (centered k s)]
  simp [centered,centered_mean,centered_second_moment]
  ring


def coordLoss (k : ℕ) (t s y z₁ z₂ : ℝ) (uv : Pair) :=
  (y-reconstruction k t uv.1*z₁-reconstruction k s uv.2*z₂)^2

theorem coordLoss_centered (k : ℕ) (t s y z₁ z₂ : ℝ) (uv : Pair) :
    coordLoss k t s y z₁ z₂ uv =
      ((y-clip k t*z₁-clip k s*z₂)+(-z₁)*centered k t uv.1+(-z₂)*centered k s uv.2)^2 := by
  dsimp [coordLoss,centered]; ring

theorem coordLoss_integrable (k : ℕ) (t s y z₁ z₂ : ℝ) :
    Integrable (coordLoss k t s y z₁ z₂) rowNoise := by
  simp_rw [funext (coordLoss_centered k t s y z₁ z₂)]
  exact centered_pair_square_integrable k t s _ _ _

theorem coordLoss_expectation (k : ℕ) (t s y z₁ z₂ : ℝ) :
    (∫ uv, coordLoss k t s y z₁ z₂ uv ∂rowNoise) =
      (y-clip k t*z₁-clip k s*z₂)^2+(z₁^2+z₂^2)/12 := by
  simp_rw [coordLoss_centered]
  rw [centered_pair_square]
  ring

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
def fSq (M : Mat) : ℝ := ∑ i, ∑ j, (M i j)^2

def reconstructed (k : ℕ) (T : Mat) (u : Pair × Pair) : Mat :=
  !![reconstruction k (T 0 0) u.1.1, reconstruction k (T 0 1) u.1.2;
     reconstruction k (T 1 0) u.2.1, reconstruction k (T 1 1) u.2.2]
def actualLoss (k : ℕ) (Y T Z : Mat) (u : Pair × Pair) :=
  fSq (Y-reconstructed k T u * Z)
def clipped (k : ℕ) (T : Mat) : Mat := fun i j => clip k (T i j)
def expectedLoss (k : ℕ) (Y T Z : Mat) := ∫ u, actualLoss k Y T Z u ∂fourNoise

def rowLoss (k : ℕ) (Y T Z : Mat) (i : Fin 2) (uv : Pair) :=
  coordLoss k (T i 0) (T i 1) (Y i 0) (Z 0 0) (Z 1 0) uv +
  coordLoss k (T i 0) (T i 1) (Y i 1) (Z 0 1) (Z 1 1) uv

theorem rowLoss_integrable (k : ℕ) (Y T Z : Mat) (i : Fin 2) :
    Integrable (rowLoss k Y T Z i) rowNoise :=
  (coordLoss_integrable k _ _ _ _ _).add (coordLoss_integrable k _ _ _ _ _)

theorem actualLoss_rows (k : ℕ) (Y T Z : Mat) (u : Pair × Pair) :
    actualLoss k Y T Z u = rowLoss k Y T Z 0 u.1 + rowLoss k Y T Z 1 u.2 := by
  simp [actualLoss,fSq,rowLoss,coordLoss,reconstructed,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  ring

theorem actualLoss_integrable (k : ℕ) (Y T Z : Mat) :
    Integrable (actualLoss k Y T Z) fourNoise := by
  simp_rw [funext (actualLoss_rows k Y T Z)]
  exact ((rowLoss_integrable k Y T Z 0).comp_fst rowNoise).add
    ((rowLoss_integrable k Y T Z 1).comp_snd rowNoise)

theorem expectedLoss_formula (k : ℕ) (Y T Z : Mat) :
    expectedLoss k Y T Z = fSq (Y-clipped k T*Z)+fSq Z/6 := by
  unfold expectedLoss
  simp_rw [actualLoss_rows]
  unfold fourNoise
  rw [integral_add ((rowLoss_integrable k Y T Z 0).comp_fst rowNoise)
    ((rowLoss_integrable k Y T Z 1).comp_snd rowNoise)]
  simp only [integral_fun_fst,integral_fun_snd,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  unfold rowLoss
  rw [integral_add (coordLoss_integrable k _ _ _ _ _) (coordLoss_integrable k _ _ _ _ _),
    integral_add (coordLoss_integrable k _ _ _ _ _) (coordLoss_integrable k _ _ _ _ _)]
  simp only [coordLoss_expectation]
  simp [clipped,fSq,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  ring
end
end QepFiniteDitherMatrix
