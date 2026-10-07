import QepX1Conditional

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace QepX1
noncomputable section
open QepCorrected QepGram QepV3
open scoped BigOperators
variable {Ω m n : Type*} [Fintype Ω] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]



def ConditionalEntryCovariance {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (K : m → n → m → n → ℝ) : Prop :=
  ∀ f : Ω → ℝ, Past history k f → ∀ i r j s,
    (∑ ω,p ω*(f ω*(E ω i r*E ω j s)))=(∑ ω,p ω*f ω)*K i r j s


def entryOperator (K : m → n → m → n → ℝ) : Mat n n →ₗ[ℝ] Mat m m where
  toFun T := fun i j => ∑ r,∑ s,K i r j s*T r s
  map_add' A B := by
    ext i j
    change (∑ r,∑ s,K i r j s*(A r s+B r s))=
      (∑ r,∑ s,K i r j s*A r s)+(∑ r,∑ s,K i r j s*B r s)
    simp only [mul_add,Finset.sum_add_distrib]
  map_smul' c A := by
    ext i j
    change (∑ r,∑ s,K i r j s*(c*A r s))=c*(∑ r,∑ s,K i r j s*A r s)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring




theorem entry_covariance_to_secondPSD {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (K : m → n → m → n → ℝ)
    (hK : ConditionalEntryCovariance history k p E K) :
    ConditionalSecondPSD history k p E (entryOperator K) := by
  intro T hTpast _
  ext i j
  rw [mean_apply]
  change (∑ ω,p ω*((E ω*T ω)*(E ω).transpose) i j)=
    ∑ r,∑ s,K i r j s*mean p T r s
  have hentry : ∀ r s,Past history k (fun ω => T ω r s) := by
    intro r s
    exact past_map history k T (fun A => A r s) hTpast
  calc
    _ = ∑ ω,∑ r,∑ s,p ω*(T ω r s*(E ω i r*E ω j s)) := by
      apply Finset.sum_congr rfl
      intro ω _
      simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ r,∑ s,∑ ω,p ω*(T ω r s*(E ω i r*E ω j s)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [hK (fun ω => T ω r s) (hentry r s) i r j s,mean_apply]
      ring



theorem entryOperator_positive_from_law {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ) (p : Ω → ℝ)
    (E : Ω → Mat m n) (K : m → n → m → n → ℝ) (law : FiniteLaw p)
    (hK : ConditionalEntryCovariance history k p E K)
    (T : Mat n n) (hT : T.PosSemidef) : (entryOperator K T).PosSemidef :=
  secondPSD_operator_positive history k p E (entryOperator K) law
    (entry_covariance_to_secondPSD history k p E K hK) T hT

end
end QepX1
