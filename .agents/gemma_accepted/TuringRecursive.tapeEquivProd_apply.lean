-- Verified by gemma_loop.py (declaration: TuringRecursive.tapeEquivProd_apply, tier: T0, attempt: 1, spec: Encoding.lean)
@[simp]
theorem tapeEquivProd_apply {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :
    tapeEquivProd T = (T.head, T.left, T.right) :=
  by
  simp [tapeEquivProd]
