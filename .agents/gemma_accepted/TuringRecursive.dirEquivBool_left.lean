-- Verified by gemma_loop.py (declaration: TuringRecursive.dirEquivBool_left, tier: T0, attempt: 1, spec: Encoding.lean)
@[simp]
theorem dirEquivBool_left : dirEquivBool .left = false :=
  by
  simp [dirEquivBool]
