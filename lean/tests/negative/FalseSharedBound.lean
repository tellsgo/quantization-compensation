import QepArtifact

-- Deliberately reverses the exact shared-error bound comparison.
example : QepSharedE.qepU (1/4) ≤ QepSharedE.baseU (1/4) := by
  obtain ⟨hb,hq,_,_⟩ := QepSharedE.exact_errors (epsilon := (1/4)) (by norm_num)
  rw [hb,hq]
  norm_num
