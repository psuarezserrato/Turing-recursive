-- Verified by gemma_loop.py (declaration: TuringRecursive.tm0CodeEquivList_apply, tier: T0, attempt: 3, spec: Uniform.lean)
@[simp]
theorem tm0CodeEquivList_apply (m : TM0Code) :
    tm0CodeEquivList m = m.table :=
  by
  simp [tm0CodeEquivList]
