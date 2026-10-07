import QepV3Network

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace QepV3
noncomputable section
open QepCorrected QepGram
open scoped BigOperators
variable {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]

def PSDLe (A B : Mat n n) : Prop := (B-A).PosSemidef

theorem psdLe_refl (A : Mat n n) : PSDLe A A := by
  simp only [PSDLe,sub_self]
  exact Matrix.PosSemidef.zero

theorem psdLe_trans (A B C : Mat n n) (hab : PSDLe A B) (hbc : PSDLe B C) : PSDLe A C := by
  have h := hbc.add hab
  have he : (C-B)+(B-A)=C-A := by abel
  change (C-A).PosSemidef
  rw [← he]
  exact h



theorem covariance_step_mono (W : Mat m n) (T Cp Cm : Mat n n)
    (Ψ : Mat n n →ₗ[ℝ] Mat m m) (cp cm : ℝ)
    (hCp : Cp.PosSemidef) (horder : PSDLe Cp Cm)
    (hcm : 0 ≤ cm) (hc : cp ≤ cm)
    (hΨ : ∀ A : Mat n n,A.PosSemidef → (Ψ A).PosSemidef) :
    PSDLe (cp • (W*Cp*W.transpose)+Ψ (Cp+T))
      (cm • (W*Cm*W.transpose)+Ψ (Cm+T)) := by
  have h1 : ((cm-cp) • (W*Cp*W.transpose)).PosSemidef := by
    have h := hCp.mul_mul_conjTranspose_same W
    simpa using h.smul (sub_nonneg.mpr hc)
  have h2 : (cm • (W*(Cm-Cp)*W.transpose)).PosSemidef := by
    have h := horder.mul_mul_conjTranspose_same W
    simpa using h.smul hcm
  have h3 := hΨ (Cm-Cp) horder
  have he : (cm • (W*Cm*W.transpose)+Ψ (Cm+T))-
      (cp • (W*Cp*W.transpose)+Ψ (Cp+T)) =
      (cm-cp) • (W*Cp*W.transpose)+cm • (W*(Cm-Cp)*W.transpose)+Ψ (Cm-Cp) := by
    simp only [map_add,map_sub,Matrix.mul_sub,Matrix.sub_mul,smul_sub,sub_smul]
    abel
  unfold PSDLe
  rw [he]
  exact (h1.add h2).add h3

variable {Ωa Ωb : Type*} [Fintype Ωa] [Fintype Ωb]



theorem actual_covariance_antitone (d : ℕ → ℕ) (N L : ℕ)
    (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (X0 : Mat (Fin (d 0)) (Fin N)) (a b : ℕ → ℝ)
    (Ea : (k : ℕ) → Ωa → Mat (Fin (d (k+1))) (Fin (d k)))
    (Eb : (k : ℕ) → Ωb → Mat (Fin (d (k+1))) (Fin (d k)))
    (pa : Ωa → ℝ) (pb : Ωb → ℝ) (lawA : FiniteLaw pa) (lawB : FiniteLaw pb)
    (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
      Mat (Fin (d (k+1))) (Fin (d (k+1))))
    (hla : Legal d N W X0 a Ea pa L) (hlb : Legal d N W X0 b Eb pb L)
    (hra : RowCondition d N W X0 a Ea pa L) (hrb : RowCondition d N W X0 b Eb pb L)
    (hma : ConditionalMoments d Ea pa Ψ L) (hmb : ConditionalMoments d Eb pb Ψ L)
    (_ha : ∀ k < L,0 ≤ a k) (hab : ∀ k < L,a k ≤ b k) (hb : ∀ k < L,b k ≤ 1) :
    PSDLe (covariance d N W X0 b Eb pb L) (covariance d N W X0 a Ea pa L) := by
  have hall : ∀ k ≤ L,
      PSDLe (covariance d N W X0 b Eb pb k) (covariance d N W X0 a Ea pa k) := by
    intro k hk
    induction k with
    | zero =>
      simp only [covariance,error,student,teacher,sub_self,Matrix.transpose_zero,Matrix.mul_zero,mean_zero]
      exact psdLe_refl _
    | succ k ih =>
      rw [actual_covariance_step d N W X0 b Eb pb L Ψ lawB hlb hrb hmb k (by omega),
        actual_covariance_step d N W X0 a Ea pa L Ψ lawA hla hra hma k (by omega)]
      apply covariance_step_mono
      · exact actual_covariance_posSemidef d N W X0 b Eb pb lawB k
      · exact ih (by omega)
      · exact sq_nonneg _
      · nlinarith [hab k (by omega),hb k (by omega)]
      · intro T hT
        exact actual_noise_operator_positive d Ea pa L Ψ lawA hma k (by omega) T hT
  exact hall L le_rfl

theorem trace_gram_eq_fSq (A : Mat m n) : (A*A.transpose).trace=fSq A := by
  simp [Matrix.trace,Matrix.mul_apply,Matrix.transpose_apply,fSq,pow_two]

theorem trace_mean {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (F : Ω → Mat n n) :
    (mean p F).trace=∑ ω,p ω*(F ω).trace := by
  simp [mean,Matrix.trace_sum,Matrix.trace_smul]

theorem trace_mean_gram {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (R : Ω → Mat m n) :
    (mean p (fun ω => R ω*(R ω).transpose)).trace=∑ ω,p ω*fSq (R ω) := by
  rw [trace_mean]
  simp only [trace_gram_eq_fSq]

theorem psdLe_trace (A B : Mat n n) (h : PSDLe A B) : A.trace ≤ B.trace := by
  have hh := h.trace_nonneg
  rw [Matrix.trace_sub] at hh
  linarith


theorem actual_frobenius_mse_antitone (d : ℕ → ℕ) (N L : ℕ)
    (W : (k : ℕ) → Mat (Fin (d (k+1))) (Fin (d k)))
    (X0 : Mat (Fin (d 0)) (Fin N)) (a b : ℕ → ℝ)
    (Ea : (k : ℕ) → Ωa → Mat (Fin (d (k+1))) (Fin (d k)))
    (Eb : (k : ℕ) → Ωb → Mat (Fin (d (k+1))) (Fin (d k)))
    (pa : Ωa → ℝ) (pb : Ωb → ℝ) (lawA : FiniteLaw pa) (lawB : FiniteLaw pb)
    (Ψ : (k : ℕ) → Mat (Fin (d k)) (Fin (d k)) →ₗ[ℝ]
      Mat (Fin (d (k+1))) (Fin (d (k+1))))
    (hla : Legal d N W X0 a Ea pa L) (hlb : Legal d N W X0 b Eb pb L)
    (hra : RowCondition d N W X0 a Ea pa L) (hrb : RowCondition d N W X0 b Eb pb L)
    (hma : ConditionalMoments d Ea pa Ψ L) (hmb : ConditionalMoments d Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (hab : ∀ k < L,a k ≤ b k) (hb : ∀ k < L,b k ≤ 1) :
    (∑ ω,pb ω*fSq (error d N W X0 b Eb L ω)) ≤
      ∑ ω,pa ω*fSq (error d N W X0 a Ea L ω) := by
  have h := psdLe_trace _ _ (actual_covariance_antitone d N L W X0 a b Ea Eb pa pb lawA lawB Ψ
    hla hlb hra hrb hma hmb ha hab hb)
  simpa only [covariance,trace_mean_gram] using h



theorem equal_width_actual_comparison (D N L : ℕ)
    (W : ℕ → Mat (Fin D) (Fin D)) (X0 : Mat (Fin D) (Fin N)) (a b : ℕ → ℝ)
    (Ea : ℕ → Ωa → Mat (Fin D) (Fin D)) (Eb : ℕ → Ωb → Mat (Fin D) (Fin D))
    (pa : Ωa → ℝ) (pb : Ωb → ℝ) (lawA : FiniteLaw pa) (lawB : FiniteLaw pb)
    (Ψ : ℕ → Mat (Fin D) (Fin D) →ₗ[ℝ] Mat (Fin D) (Fin D))
    (hrow : LinearIndependent ℝ X0.row)
    (hweightA : ∀ k < L, ∀ ω,pa ω ≠ 0 → IsUnit
      (correctedWeight (W k) (teacher (fun _ => D) N W X0 k)
        (student (fun _ => D) N W X0 a Ea k ω) (a k)+Ea k ω).det)
    (hweightB : ∀ k < L, ∀ ω,pb ω ≠ 0 → IsUnit
      (correctedWeight (W k) (teacher (fun _ => D) N W X0 k)
        (student (fun _ => D) N W X0 b Eb k ω) (b k)+Eb k ω).det)
    (hma : ConditionalMoments (fun _ => D) Ea pa Ψ L)
    (hmb : ConditionalMoments (fun _ => D) Eb pb Ψ L)
    (ha : ∀ k < L,0 ≤ a k) (hab : ∀ k < L,a k ≤ b k) (hb : ∀ k < L,b k ≤ 1) :
    PSDLe (covariance (fun _ => D) N W X0 b Eb pb L) (covariance (fun _ => D) N W X0 a Ea pa L) ∧
    (∑ ω,pb ω*fSq (error (fun _ => D) N W X0 b Eb L ω)) ≤
      ∑ ω,pa ω*fSq (error (fun _ => D) N W X0 a Ea L ω) := by
  obtain ⟨hla,hra⟩ := actual_equal_width_sufficient D N L W X0 a Ea pa hrow hweightA
  obtain ⟨hlb,hrb⟩ := actual_equal_width_sufficient D N L W X0 b Eb pb hrow hweightB
  exact ⟨actual_covariance_antitone (fun _ => D) N L W X0 a b Ea Eb pa pb lawA lawB Ψ
    hla hlb hra hrb hma hmb ha hab hb,
    actual_frobenius_mse_antitone (fun _ => D) N L W X0 a b Ea Eb pa pb lawA lawB Ψ
    hla hlb hra hrb hma hmb ha hab hb⟩

end
end QepV3
