import QepSharedE




set_option autoImplicit false
namespace QepSharedEExtended
noncomputable section
open QepSharedE

structure InvertibleLegal (epsilon : ℝ) : Prop where
  identity_conditions : activation 0 = 0 ∧ ∀ x y : ℝ, |activation x-activation y| ≤ 1*|x-y|
  alpha_conditions : (0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1
  teacher_nonzero : fixed.w1 ≠ 0 ∧ fixed.w2 ≠ 0
  weight_nonzero : (baseRun epsilon).weight1 ≠ 0 ∧ (baseRun epsilon).weight2 ≠ 0 ∧
    (qepRun epsilon).weight1 ≠ 0 ∧ (qepRun epsilon).weight2 ≠ 0
  gram_positive : 0 < gram fixed.input ∧ 0 < gram (teacher2 fixed) ∧
    0 < gram (baseRun epsilon).input1 ∧ 0 < gram (baseRun epsilon).input2 ∧
    0 < gram (qepRun epsilon).input1 ∧ 0 < gram (qepRun epsilon).input2

theorem nonzero_qep_weight_iff {epsilon : ℝ} (he : 0 < epsilon) :
    (qepRun epsilon).weight2 ≠ 0 ↔ epsilon^2+epsilon ≠ 1 := by
  rw [qep_closed he]
  dsimp
  have hd : 1+epsilon ≠ 0 := by linarith
  constructor
  · intro hn h
    apply hn
    field_simp
    nlinarith
  · intro hn h
    apply hn
    have hh : (1:ℝ)/(1+epsilon) = epsilon := by linarith
    have hh' := (div_eq_iff hd).mp hh
    nlinarith

theorem invertible_legal {epsilon : ℝ} (he : 0 < epsilon)
    (hb : epsilon ≠ 1) (hq : epsilon^2+epsilon ≠ 1) : InvertibleLegal epsilon := by
  have hd : 1+epsilon ≠ 0 := by linarith
  have hb' : 1-epsilon ≠ 0 := by intro h; apply hb; linarith
  have hq' := (nonzero_qep_weight_iff he).mpr hq
  refine ⟨identity_lipschitz,by norm_num,by norm_num [fixed],?_,?_⟩
  · rw [qep_closed he] at hq'
    rw [base_closed,qep_closed he]
    exact ⟨hd,hb',hd,hq'⟩
  · rw [base_closed,qep_closed he]
    norm_num [gram,fixed,teacher2,activation]
    positivity

theorem no_upper_bound_core {epsilon : ℝ} (he : 0 < epsilon)
    (hb : epsilon ≠ 1) (hq : epsilon^2+epsilon ≠ 1) :
    InvertibleLegal epsilon ∧
    qepU epsilon-baseU epsilon = epsilon ∧ baseU epsilon < qepU epsilon ∧
    baseErr epsilon = epsilon^2 ∧ qepErr epsilon = epsilon+epsilon^2 ∧
    baseErr epsilon < qepErr epsilon := by
  obtain ⟨hbU,hqU,hbE,hqE⟩ := exact_errors he
  refine ⟨invertible_legal he hb hq,?_,?_,hbE,hqE,?_⟩
  · rw [hbU,hqU]; ring
  · rw [hbU,hqU]; linarith
  · rw [hbE,hqE]; linarith

theorem epsilon_one_not_legal : ¬ InvertibleLegal 1 := by
  intro h
  have hn := h.weight_nonzero.2.1
  rw [base_closed] at hn
  norm_num at hn

theorem singular_qep_not_legal {epsilon : ℝ} (he : 0 < epsilon)
    (hs : epsilon^2+epsilon = 1) : ¬ InvertibleLegal epsilon := by
  intro h
  exact (nonzero_qep_weight_iff he).mp h.weight_nonzero.2.2.2 hs

theorem exact_legal_domain {epsilon : ℝ} (he : 0 < epsilon) :
    InvertibleLegal epsilon ↔ epsilon ≠ 1 ∧ epsilon^2+epsilon ≠ 1 := by
  constructor
  · intro h
    constructor
    · intro heq
      subst epsilon
      exact epsilon_one_not_legal h
    · exact (nonzero_qep_weight_iff he).mp h.weight_nonzero.2.2.2
  · intro h
    exact invertible_legal he h.1 h.2

end
end QepSharedEExtended
