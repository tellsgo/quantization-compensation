import QepFiniteMomentAssembly
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
open MeasureTheory Function
open QepFiniteDitherLaw QepFiniteDitherHistory QepContinuousCoordinates
namespace QepActualFiniteMoments
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

def centered (k : ℕ) (t : ι → ℝ) (i : ι) (u : ι → ℝ) := reconstruction k (t i) (u i)-clip k (t i)

theorem centered_joint_measurable (k : ℕ) (t : ι → ℝ) :
    Measurable (fun u i => centered k t i u) := by
  apply measurable_pi_iff.mpr; intro i
  exact ((reconstruction_measurable k (t i)).comp (measurable_pi_apply i)).sub measurable_const

theorem centered_joint_law (k : ℕ) (t : ι → ℝ) :
    Measure.map (fun u i => centered k t i u) law=law :=
  finite_family_joint_law k t

theorem transfer_integral (k : ℕ) (t : ι → ℝ) (g : (ι → ℝ) → ℝ)
    (hg : StronglyMeasurable g) :
    (∫ u, g (fun i => centered k t i u) ∂law)=∫ u, g u ∂law := by
  have h := integral_map_of_stronglyMeasurable (centered_joint_measurable k t) hg (μ:=law)
  rw [centered_joint_law] at h
  exact h.symm

theorem transfer_integrable (k : ℕ) (t : ι → ℝ) (g : (ι → ℝ) → ℝ)
    (hg : StronglyMeasurable g) (hi : Integrable g law) :
    Integrable (fun u => g (fun i => centered k t i u)) law := by
  have h : Integrable g (Measure.map (fun u i => centered k t i u) law) := by
    rw [centered_joint_law]; exact hi
  exact (integrable_map_measure hg.aestronglyMeasurable
    (centered_joint_measurable k t).aemeasurable).mp h

theorem centered_integrable (k : ℕ) (t : ι → ℝ) (i : ι) :
    Integrable (centered k t i) law :=
  transfer_integrable k t (fun u => u i) (measurable_pi_apply i).stronglyMeasurable (eval_integrable i)

theorem centered_pair_integrable (k : ℕ) (t : ι → ℝ) (i j : ι) :
    Integrable (fun u => centered k t i u*centered k t j u) law :=
  transfer_integrable k t (fun u => u i*u j) (by fun_prop) (pair_integrable i j)

theorem centered_mean (k : ℕ) (t : ι → ℝ) (i : ι) :
    (∫ u, centered k t i u ∂law)=0 :=
  (transfer_integral k t (fun u => u i) (measurable_pi_apply i).stronglyMeasurable).trans (eval_mean i)

theorem centered_covariance (k : ℕ) (t : ι → ℝ) (i j : ι) :
    (∫ u, centered k t i u*centered k t j u ∂law)=if i=j then (1/12:ℝ) else 0 :=
  (transfer_integral k t (fun u => u i*u j) (by fun_prop)).trans (pair_expectation i j)


def affineCentered (k : ℕ) (a Δ t : ι → ℝ) (i : ι) (u : ι → ℝ) :=
  scaledReconstruction (a i) (Δ i) k (t i) (u i)-scaledClip (a i) (Δ i) k (t i)

theorem affine_center_identity (k : ℕ) (a Δ t : ι → ℝ) (hΔ : ∀ i, 0<Δ i) (i : ι) (u : ι → ℝ) :
    affineCentered k a Δ t i u=Δ i*centered k (fun j => (t j-a j)/Δ j) i u :=
  scaled_reconstruction_identity (a i) (Δ i) (ne_of_gt (hΔ i)) k (t i) (u i)

theorem affine_integrable (k : ℕ) (a Δ t : ι → ℝ) (hΔ : ∀ i, 0<Δ i) (i : ι) :
    Integrable (affineCentered k a Δ t i) law := by
  simp_rw [funext (affine_center_identity k a Δ t hΔ i)]
  exact (centered_integrable k _ i).const_mul _

theorem affine_pair_integrable (k : ℕ) (a Δ t : ι → ℝ) (hΔ : ∀ i, 0<Δ i) (i j : ι) :
    Integrable (fun u => affineCentered k a Δ t i u*affineCentered k a Δ t j u) law := by
  have h : (fun u => affineCentered k a Δ t i u*affineCentered k a Δ t j u) =
      (fun u => (Δ i*Δ j)*(centered k (fun l => (t l-a l)/Δ l) i u*centered k (fun l => (t l-a l)/Δ l) j u)) := by
    funext u; rw [affine_center_identity k a Δ t hΔ i,affine_center_identity k a Δ t hΔ j]; ring
  rw [h]
  exact (centered_pair_integrable k _ i j).const_mul _

theorem affine_mean (k : ℕ) (a Δ t : ι → ℝ) (hΔ : ∀ i, 0<Δ i) (i : ι) :
    (∫ u, affineCentered k a Δ t i u ∂law)=0 := by
  simp_rw [affine_center_identity k a Δ t hΔ i]
  rw [integral_const_mul,centered_mean]; ring

theorem affine_covariance (k : ℕ) (a Δ t : ι → ℝ) (hΔ : ∀ i, 0<Δ i) (i j : ι) :
    (∫ u, affineCentered k a Δ t i u*affineCentered k a Δ t j u ∂law)=
      if i=j then (Δ i)^2/12 else 0 := by
  have h : (fun u => affineCentered k a Δ t i u*affineCentered k a Δ t j u) =
      (fun u => (Δ i*Δ j)*(centered k (fun l => (t l-a l)/Δ l) i u*centered k (fun l => (t l-a l)/Δ l) j u)) := by
    funext u; rw [affine_center_identity k a Δ t hΔ i,affine_center_identity k a Δ t hΔ j]; ring
  rw [h,integral_const_mul,centered_covariance]
  by_cases hij : i=j
  · subst j; simp; ring
  · simp [hij]
end
end QepActualFiniteMoments
