import QepV3RowSpace

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV3
noncomputable section
open QepCorrected QepGram
open scoped BigOperators
variable {Ω m n t : Type*} [Fintype Ω] [Fintype m] [Fintype n] [Fintype t]

def mean (p : Ω → ℝ) (F : Ω → Mat m n) : Mat m n := ∑ ω, p ω • F ω

structure FiniteLaw (p : Ω → ℝ) : Prop where
  nonnegative : ∀ ω, 0 ≤ p ω
  mass : ∑ ω, p ω=1


def Past {H : ℕ → Type*} (e : (k : ℕ) → Ω → H k) (k : ℕ) {β : Type*} (f : Ω → β) : Prop :=
  ∀ ω η, (∀ j < k, e j ω=e j η) → f ω=f η

theorem past_map {H : ℕ → Type*} (e : (k : ℕ) → Ω → H k) (k : ℕ)
    {β δ : Type*} (f : Ω → β) (g : β → δ) (hf : Past e k f) :
    Past e k (fun ω => g (f ω)) := by
  intro ω η h
  change g (f ω)=g (f η)
  rw [hf ω η h]

theorem past_pair {H : ℕ → Type*} (e : (k : ℕ) → Ω → H k) (k : ℕ)
    {β δ : Type*} (f : Ω → β) (g : Ω → δ) (hf : Past e k f) (hg : Past e k g) :
    Past e k (fun ω => (f ω,g ω)) := by
  intro ω η h
  change (f ω,g ω)=(f η,g η)
  rw [hf ω η h,hg ω η h]

theorem mean_apply (p : Ω → ℝ) (F : Ω → Mat m n) (i : m) (j : n) :
    mean p F i j=∑ ω,p ω*F ω i j := by simp [mean,Matrix.sum_apply]

theorem mean_add (p : Ω → ℝ) (F G : Ω → Mat m n) :
    mean p (fun ω => F ω+G ω)=mean p F+mean p G := by simp [mean,smul_add,Finset.sum_add_distrib]

theorem mean_sub (p : Ω → ℝ) (F G : Ω → Mat m n) :
    mean p (fun ω => F ω-G ω)=mean p F-mean p G := by simp [mean,smul_sub,Finset.sum_sub_distrib]

theorem mean_smul (p : Ω → ℝ) (F : Ω → Mat m n) (a : ℝ) :
    mean p (fun ω => a • F ω)=a • mean p F := by
  unfold mean
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact smul_comm (p ω) a (F ω)

theorem mean_const (p : Ω → ℝ) (A : Mat m n) (hp : ∑ ω,p ω=1) :
    mean p (fun _ => A)=A := by rw [mean,← Finset.sum_smul,hp,one_smul]

theorem mean_zero (p : Ω → ℝ) : mean p (fun _ => (0 : Mat m n))=0 := by simp [mean]

theorem mean_mul_const (p : Ω → ℝ) (F : Ω → Mat m n) (A : Mat n t) :
    mean p (fun ω => F ω*A)=mean p F*A := by
  simp [mean,Matrix.sum_mul,Matrix.smul_mul]

theorem mean_const_mul (p : Ω → ℝ) (A : Mat m n) (F : Ω → Mat n t) :
    mean p (fun ω => A*F ω)=A*mean p F := by
  simp [mean,Matrix.mul_sum,Matrix.mul_smul]

theorem mean_transpose (p : Ω → ℝ) (F : Ω → Mat m n) :
    mean p (fun ω => (F ω).transpose)=(mean p F).transpose := by
  ext i j
  simp [mean_apply,Matrix.transpose_apply]

theorem mean_support_congr (p : Ω → ℝ) (F G : Ω → Mat m n)
    (h : ∀ ω,p ω ≠ 0 → F ω=G ω) : mean p F=mean p G := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : p ω=0
  · simp [hp]
  · rw [h ω hp]

theorem mean_linear_map (p : Ω → ℝ) {r s : Type*} [Fintype r] [Fintype s]
    (F : Ω → Mat m n) (Ψ : Mat m n →ₗ[ℝ] Mat r s) :
    mean p (fun ω => Ψ (F ω))=Ψ (mean p F) := by simp [mean,map_sum]

theorem mean_posSemidef (p : Ω → ℝ) (F : Ω → Mat n n)
    (hp : ∀ ω,0 ≤ p ω) (hF : ∀ ω,(F ω).PosSemidef) : (mean p F).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro ω _
  exact (hF ω).smul (hp ω)

theorem mean_gram_posSemidef (p : Ω → ℝ) (R : Ω → Mat m n)
    (hp : ∀ ω,0 ≤ p ω) : (mean p (fun ω => R ω*(R ω).transpose)).PosSemidef := by
  apply mean_posSemidef p _ hp
  intro ω
  simpa using Matrix.posSemidef_self_mul_conjTranspose (R ω)


theorem mean_shifted_gram (p : Ω → ℝ) (R : Ω → Mat m n) (X : Mat m n)
    (hp : ∑ ω,p ω=1) (hR : mean p R=0) :
    mean p (fun ω => (R ω+X)*(R ω+X).transpose)=
      mean p (fun ω => R ω*(R ω).transpose)+X*X.transpose := by
  simp only [Matrix.transpose_add,Matrix.add_mul,Matrix.mul_add,mean_add,
    mean_mul_const,mean_const_mul,mean_transpose,mean_const p _ hp,hR,
    Matrix.zero_mul,Matrix.transpose_zero,Matrix.mul_zero,add_zero,zero_add]



theorem mean_noise_mul_zero {H : ℕ → Type*} (history : (k : ℕ) → Ω → H k) (k : ℕ)
    (p : Ω → ℝ) (E : Ω → Mat m n) (B : Ω → Mat n t) (hB : Past history k B)
    (hfirst : ∀ f : Ω → ℝ, Past history k f → ∀ i j,
      (∑ ω,p ω*(f ω*E ω i j))=0) : mean p (fun ω => E ω*B ω)=0 := by
  ext i j
  rw [mean_apply]
  simp only [Matrix.mul_apply,Matrix.zero_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l _
  have h := hfirst (fun ω => B ω l j) (past_map history k B (fun M => M l j) hB) i l
  convert h using 1
  apply Finset.sum_congr rfl
  intro ω _; ring

theorem mean_past_mul_noise_transpose_zero {H : ℕ → Type*}
    (history : (k : ℕ) → Ω → H k) (k : ℕ)
    (p : Ω → ℝ) (E : Ω → Mat m n) (A : Ω → Mat t n) (hA : Past history k A)
    (hfirst : ∀ f : Ω → ℝ, Past history k f → ∀ i j,
      (∑ ω,p ω*(f ω*E ω i j))=0) : mean p (fun ω => A ω*(E ω).transpose)=0 := by
  ext i j
  rw [mean_apply]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.zero_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l _
  exact hfirst (fun ω => A ω i l) (past_map history k A (fun M => M i l) hA) j l

end
end QepV3
