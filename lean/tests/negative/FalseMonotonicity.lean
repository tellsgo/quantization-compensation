import QepArtifact

-- Deliberately reverses the exact increase with correction strength.
example : QepAlpha.error (1/4) 1 ≤ QepAlpha.error (1/4) 0 := by
  rw [QepAlpha.error_closed (by norm_num) (by norm_num),
      QepAlpha.error_closed (by norm_num) (by norm_num)]
  norm_num
