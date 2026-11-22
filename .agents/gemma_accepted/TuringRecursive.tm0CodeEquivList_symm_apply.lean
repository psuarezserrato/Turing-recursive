-- Verified by gemma_loop.py (declaration: TuringRecursive.tm0CodeEquivList_symm_apply, tier: T0, attempt: 1, spec: Uniform.lean)
@[simp]
theorem tm0CodeEquivList_symm_apply (t : List (List (Option (ℕ × TM0.Stmt ℕ)))) :
    tm0CodeEquivList.symm t = ⟨t⟩ :=
  by
  simp [tm0CodeEquivList]
