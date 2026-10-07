import QepArtifact

-- Deliberately negates the sign of the actual 2-by-3 matrix bound gap.
example : QepMatrixFamily.qepU QepMatrixFamily.X23 (1/4) -
    QepMatrixFamily.baseU QepMatrixFamily.X23 (1/4) = -(1/2) := by
  have h := (QepMatrixFamily.X23_core (e := (1/4)) (by norm_num)).2.2.1
  norm_num at h ⊢
  linarith
