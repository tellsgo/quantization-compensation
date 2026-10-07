import QepArtifact

namespace FiniteNoiseControl
noncomputable def r (i : Fin 2) : ℝ := if i=0 then -1 else 1
-- Deliberately drops the first-layer noise term. The four-point product law
-- has zero means, unit variances, and nonzero first-layer quantized weights.
example : (∑ i : Fin 2, ∑ j : Fin 2, (1/4 : ℝ) *
    (QepSharedE.terminalError ⟨2,1,1,1,1⟩
      (QepSharedE.qepTrace ⟨2,1,1,1,1⟩ ⟨r i,r j⟩ 1 0))^2) = 5 := by
  norm_num [r,Fin.sum_univ_succ,QepSharedE.terminalError,QepSharedE.qepTrace,
    QepSharedE.teacherOutput,QepSharedE.teacher2,QepSharedE.activation,
    QepSharedE.corrected,QepSharedE.gram]
end FiniteNoiseControl
