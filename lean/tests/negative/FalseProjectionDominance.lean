import QepArtifact

-- Deliberately asserts that correction cannot increase this residual.
example : QepCorrected.fSq (QepProjectionExample.w*QepProjectionExample.x-
    (QepProjectionExample.wstar+QepProjectionExample.e)*QepProjectionExample.xhat) ≤
    QepCorrected.fSq (QepProjectionExample.w*QepProjectionExample.x-
    (QepProjectionExample.w+QepProjectionExample.e)*QepProjectionExample.xhat) := by
  rw [QepProjectionExample.squared_residuals.1,QepProjectionExample.squared_residuals.2]
  norm_num
