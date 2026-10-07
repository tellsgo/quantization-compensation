import QepArtifact

example : QepSharedE.baseU (1/4) < QepSharedE.qepU (1/4) := by
  obtain ⟨hb,hq,_,_⟩ := QepSharedE.exact_errors (epsilon := (1/4)) (by norm_num)
  rw [hb,hq]
  norm_num

example : QepCorrected.fSq (QepProjectionExample.w*QepProjectionExample.x-
    (QepProjectionExample.wstar+QepProjectionExample.e)*QepProjectionExample.xhat) = 2 :=
  QepProjectionExample.squared_residuals.2

example : QepInterior.qepMsgAlpha2 (3/4) (7/5) 2 (18/25) = (1,3,1) :=
  QepInterior.alpha_three_quarters_message

example : ¬ QepSharedEExtended.InvertibleLegal 1 :=
  QepSharedEExtended.epsilon_one_not_legal

example : QepMatrixFamily.qepU QepMatrixFamily.X23 (1/4) -
    QepMatrixFamily.baseU QepMatrixFamily.X23 (1/4) = 1/2 := by
  have h := (QepMatrixFamily.X23_core (e := (1/4)) (by norm_num)).2.2.1
  norm_num at h ⊢
  exact h

namespace FiniteNoiseControl
noncomputable def r (i : Fin 2) : ℝ := if i=0 then -1 else 1
example : (∑ i : Fin 2, ∑ j : Fin 2, (1/4 : ℝ) *
    (QepSharedE.terminalError ⟨2,1,1,1,1⟩
      (QepSharedE.qepTrace ⟨2,1,1,1,1⟩ ⟨r i,r j⟩ 1 0))^2) = 6 := by
  norm_num [r,Fin.sum_univ_succ,QepSharedE.terminalError,QepSharedE.qepTrace,
    QepSharedE.teacherOutput,QepSharedE.teacher2,QepSharedE.activation,
    QepSharedE.corrected,QepSharedE.gram]
end FiniteNoiseControl
