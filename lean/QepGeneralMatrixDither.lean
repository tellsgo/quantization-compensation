import QepActualFiniteMoments
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open MeasureTheory Matrix QepFiniteDitherLaw QepContinuousCoordinates QepFiniteMomentAssembly
namespace QepGeneralMatrixDither
noncomputable section
attribute [local instance] Classical.propDecidable
variable {m n s : Type*} [Fintype m] [Fintype n] [Fintype s]

abbrev Primitive (m n : Type*) := (m × n) → ℝ

def reconstructed (k : ℕ) (a Δ T : Matrix m n ℝ) (u : Primitive m n) : Matrix m n ℝ :=
  fun i j => scaledReconstruction (a i j) (Δ i j) k (T i j) (u (i,j))
def clipped (k : ℕ) (a Δ T : Matrix m n ℝ) : Matrix m n ℝ :=
  fun i j => scaledClip (a i j) (Δ i j) k (T i j)
def rowCentered (k : ℕ) (a Δ T : Matrix m n ℝ) (i : m) (j : n) (u : Primitive m n) :=
  QepActualFiniteMoments.affineCentered k (fun p => a p.1 p.2) (fun p => Δ p.1 p.2)
    (fun p => T p.1 p.2) (i,j) u

theorem row_moments (k : ℕ) (a Δ T : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j) (i : m) :
    (∀ j, Integrable (rowCentered k a Δ T i j) law) ∧
    (∀ j l, Integrable (fun u => rowCentered k a Δ T i j u*rowCentered k a Δ T i l u) law) ∧
    (∀ j, (∫ u, rowCentered k a Δ T i j u ∂law)=0) ∧
    (∀ j l, (∫ u, rowCentered k a Δ T i j u*rowCentered k a Δ T i l u ∂law)=
      if j=l then (Δ i j)^2/12 else 0) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j; exact QepActualFiniteMoments.affine_integrable k _ _ _ (fun p => hΔ p.1 p.2) (i,j)
  · intro j l; exact QepActualFiniteMoments.affine_pair_integrable k _ _ _ (fun p => hΔ p.1 p.2) (i,j) (i,l)
  · intro j; exact QepActualFiniteMoments.affine_mean k _ _ _ (fun p => hΔ p.1 p.2) (i,j)
  · intro j l
    simpa only [rowCentered, Prod.mk.injEq, true_and] using
      QepActualFiniteMoments.affine_covariance k (fun p => a p.1 p.2) (fun p => Δ p.1 p.2)
        (fun p => T p.1 p.2) (fun p => hΔ p.1 p.2) (i,j) (i,l)

theorem actual_coordinate_identity (k : ℕ) (a Δ T : Matrix m n ℝ)
    (Y : Matrix m s ℝ) (Z : Matrix n s ℝ) (i : m) (t : s) (u : Primitive m n) :
    Y i t-(reconstructed k a Δ T u*Z) i t =
      (Y i t-(clipped k a Δ T*Z) i t)-
      linear (rowCentered k a Δ T i) (fun j => Z j t) u := by
  have h : (reconstructed k a Δ T u*Z) i t =
      (clipped k a Δ T*Z) i t+linear (rowCentered k a Δ T i) (fun j => Z j t) u := by
    simp only [Matrix.mul_apply,linear,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j hj
    dsimp [reconstructed,clipped,rowCentered,QepActualFiniteMoments.affineCentered]
    ring
  rw [h]; ring

def coordinateLoss (k : ℕ) (a Δ T : Matrix m n ℝ) (Y : Matrix m s ℝ)
    (Z : Matrix n s ℝ) (i : m) (t : s) (u : Primitive m n) :=
  (Y i t-(reconstructed k a Δ T u*Z) i t)^2

theorem actual_coordinate_integrable (k : ℕ) (a Δ T : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (Y : Matrix m s ℝ) (Z : Matrix n s ℝ) (i : m) (t : s) :
    Integrable (coordinateLoss k a Δ T Y Z i t) law := by
  have h := row_moments k a Δ T hΔ i
  unfold coordinateLoss
  simp_rw [actual_coordinate_identity]
  exact affine_square_integrable law _ _ _ h.1 h.2.1

theorem actual_coordinate_expectation (k : ℕ) (a Δ T : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (Y : Matrix m s ℝ) (Z : Matrix n s ℝ) (i : m) (t : s) :
    (∫ u, coordinateLoss k a Δ T Y Z i t u ∂law)=
      (Y i t-(clipped k a Δ T*Z) i t)^2+∑ j, (Z j t)^2*((Δ i j)^2/12) := by
  have h := row_moments k a Δ T hΔ i
  unfold coordinateLoss
  simp_rw [actual_coordinate_identity]
  exact affine_square_expectation law _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

def fSq (A : Matrix m s ℝ) := ∑ i, ∑ t, (A i t)^2

def actualLoss (k : ℕ) (a Δ T : Matrix m n ℝ) (Y : Matrix m s ℝ)
    (Z : Matrix n s ℝ) (u : Primitive m n) := fSq (Y-reconstructed k a Δ T u*Z)
def noiseEnergy (Δ : Matrix m n ℝ) (Z : Matrix n s ℝ) := ∑ i, ∑ t, ∑ j, (Z j t)^2*((Δ i j)^2/12)

theorem actual_loss_integrable (k : ℕ) (a Δ T : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (Y : Matrix m s ℝ) (Z : Matrix n s ℝ) : Integrable (actualLoss k a Δ T Y Z) law := by
  exact integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun t _ => actual_coordinate_integrable k a Δ T hΔ Y Z i t))

theorem actual_matrix_expected_loss (k : ℕ) (a Δ T : Matrix m n ℝ) (hΔ : ∀ i j,0<Δ i j)
    (Y : Matrix m s ℝ) (Z : Matrix n s ℝ) :
    (∫ u, actualLoss k a Δ T Y Z u ∂law)=fSq (Y-clipped k a Δ T*Z)+noiseEnergy Δ Z := by
  change (∫ u, ∑ i, ∑ t, coordinateLoss k a Δ T Y Z i t u ∂law)=_
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun t _ => actual_coordinate_integrable k a Δ T hΔ Y Z i t))]
  simp_rw [integral_finsetSum Finset.univ (fun t _ => actual_coordinate_integrable k a Δ T hΔ Y Z _ t),
    actual_coordinate_expectation k a Δ T hΔ Y Z]
  simp [fSq,noiseEnergy,Finset.sum_add_distrib]
end
end QepGeneralMatrixDither
