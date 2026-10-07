import QepArtifact

-- Deliberately contradicts the zero second-layer weight at epsilon=1.
example : QepSharedEExtended.InvertibleLegal 1 := by
  have h : (QepSharedE.baseRun 1).weight2 ≠ 0 := by
    rw [QepSharedE.base_closed]
    norm_num
  exact False.elim (h (by rw [QepSharedE.base_closed]; norm_num))
