import QepV3Conditional

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV3
noncomputable section
open QepCorrected QepGram
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

variable (d : ℕ → ℕ) (N : ℕ)
variable (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
variable (X0 : Mat (Fin (d 0)) (Fin N)) (α : ℕ → ℝ)
variable (E : (k : ℕ) → Ω → Mat (Fin (d (k+1))) (Fin (d k)))

def teacher : (k : ℕ) → Mat (Fin (d k)) (Fin N)
  | 0 => X0
  | k+1 => W k*teacher k



def student : (k : ℕ) → Ω → Mat (Fin (d k)) (Fin N)
  | 0 => fun _ => X0
  | k+1 => fun ω =>
      (correctedWeight (W k) (teacher d N W X0 k) (student k ω) (α k)+E k ω)*
      student k ω

def error (k : ℕ) (ω : Ω) : Mat (Fin (d k)) (Fin N) :=
  student d N W X0 α E k ω-teacher d N W X0 k

def covariance (p : Ω → ℝ) (k : ℕ) : Mat (Fin (d k)) (Fin (d k)) :=
  mean p (fun ω => error d N W X0 α E k ω*(error d N W X0 α E k ω).transpose)

def Legal (p : Ω → ℝ) (L : ℕ) : Prop :=
  ∀ k < L, ∀ ω,p ω ≠ 0 → IsUnit (gram (student d N W X0 α E k ω)).det

def RowCondition (p : Ω → ℝ) (L : ℕ) : Prop :=
  ∀ k < L, ∀ ω,p ω ≠ 0 →
    teacher d N W X0 k*gramProjection (student d N W X0 α E k ω)=teacher d N W X0 k

structure ConditionalMoments (p : Ω → ℝ)
    (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
      Mat (Fin (d (k+1))) (Fin (d (k+1)))) (L : ℕ) : Prop where
  first : ∀ k < L, ConditionalMeanZero E k p (E k)
  second : ∀ k < L, ConditionalSecondOperator E k p (E k) (Ψ k)

theorem past_student (k : ℕ) : Past E k (student d N W X0 α E k) := by
  induction k with
  | zero => intro ω η h; rfl
  | succ k ih =>
    intro ω η h
    have hz := ih ω η (fun j hj => h j (by omega))
    simp only [student,hz,h k (Nat.lt_succ_self k)]

theorem past_error (k : ℕ) : Past E k (error d N W X0 α E k) :=
  past_map E k (student d N W X0 α E k) (fun Z => Z-teacher d N W X0 k)
    (past_student d N W X0 α E k)

variable (p : Ω → ℝ) (L : ℕ)
variable (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
    Mat (Fin (d (k+1))) (Fin (d (k+1))))


theorem actual_mean_zero
    (hl : Legal d N W X0 α E p L) (hr : RowCondition d N W X0 α E p L)
    (hm : ConditionalMoments d E p Ψ L) (k : ℕ) (hk : k ≤ L) :
    mean p (error d N W X0 α E k)=0 := by
  induction k with
  | zero => simp [error,student,teacher,mean]
  | succ k ih =>
    change mean p (fun ω =>
      (correctedWeight (W k) (teacher d N W X0 k) (student d N W X0 α E k ω) (α k)+E k ω)*
      student d N W X0 α E k ω-W k*teacher d N W X0 k)=0
    rw [actual_layer_mean E k p (E k) (student d N W X0 α E k) (W k) (teacher d N W X0 k) (α k)
      (past_student d N W X0 α E k) (hm.first k (by omega))
      (hl k (by omega)) (hr k (by omega))]
    change (1-α k) • (W k*mean p (error d N W X0 α E k))=0
    rw [ih (by omega),Matrix.mul_zero,smul_zero]


theorem actual_covariance_step (law : FiniteLaw p)
    (hl : Legal d N W X0 α E p L) (hr : RowCondition d N W X0 α E p L)
    (hm : ConditionalMoments d E p Ψ L) (k : ℕ) (hk : k < L) :
    covariance d N W X0 α E p (k+1)=
      (1-α k)^2 • (W k*covariance d N W X0 α E p k*(W k).transpose)+
      Ψ k (covariance d N W X0 α E p k+teacher d N W X0 k*(teacher d N W X0 k).transpose) := by
  exact actual_layer_second_moment E k p (E k) (student d N W X0 α E k)
    (W k) (teacher d N W X0 k) (α k) (Ψ k) law
    (past_student d N W X0 α E k) (hm.first k hk) (hm.second k hk) (hl k hk) (hr k hk)
    (actual_mean_zero d N W X0 α E p L Ψ hl hr hm k (by omega))

theorem actual_covariance_posSemidef (law : FiniteLaw p) (k : ℕ) :
    (covariance d N W X0 α E p k).PosSemidef :=
  mean_gram_posSemidef p (error d N W X0 α E k) law.nonnegative


theorem actual_noise_operator_positive (law : FiniteLaw p)
    (hm : ConditionalMoments d E p Ψ L) (k : ℕ) (hk : k < L)
    (T : Mat (Fin (d k)) (Fin (d k))) (hT : T.PosSemidef) : (Ψ k T).PosSemidef :=
  conditional_operator_positive E k p (E k) (Ψ k) law (hm.second k hk) T hT



theorem actual_equal_width_sufficient (D : ℕ) (N L : ℕ)
    (W : ℕ → Mat (Fin D) (Fin D)) (X0 : Mat (Fin D) (Fin N)) (α : ℕ → ℝ)
    (E : ℕ → Ω → Mat (Fin D) (Fin D)) (p : Ω → ℝ)
    (hrow : LinearIndependent ℝ X0.row)
    (hweight : ∀ k < L, ∀ ω,p ω ≠ 0 → IsUnit
      (correctedWeight (W k) (teacher (fun _ => D) N W X0 k)
        (student (fun _ => D) N W X0 α E k ω) (α k)+E k ω).det) :
    Legal (fun _ => D) N W X0 α E p L ∧ RowCondition (fun _ => D) N W X0 α E p L := by
  have hall : ∀ k ≤ L, ∀ ω,p ω ≠ 0 →
      IsUnit (gram (student (fun _ => D) N W X0 α E k ω)).det ∧
      teacher (fun _ => D) N W X0 k*gramProjection (student (fun _ => D) N W X0 α E k ω)=
        teacher (fun _ => D) N W X0 k := by
    intro k hk ω hω
    apply equal_width_row_condition W
      (fun j => correctedWeight (W j) (teacher (fun _ => D) N W X0 j)
        (student (fun _ => D) N W X0 α E j ω) (α j)+E j ω)
      (teacher (fun _ => D) N W X0) (fun j => student (fun _ => D) N W X0 α E j ω) L
      rfl hrow (fun j hj => rfl) (fun j hj => rfl) (fun j hj => hweight j hj ω hω) k hk
  exact ⟨fun k hk ω hω => (hall k (by omega) ω hω).1,
    fun k hk ω hω => (hall k (by omega) ω hω).2⟩

end
end QepV3
