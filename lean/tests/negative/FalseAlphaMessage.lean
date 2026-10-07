import QepArtifact

-- Deliberately uses the half-strength code at three-quarter strength.
example : QepInterior.qepMsgAlpha2 (3/4) (7/5) 2 (18/25) = (1,2,1) := by
  rw [QepInterior.alpha_three_quarters_message]
  norm_num
