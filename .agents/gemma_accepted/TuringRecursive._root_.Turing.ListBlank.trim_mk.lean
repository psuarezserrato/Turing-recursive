-- Verified by gemma_loop.py (declaration: TuringRecursive._root_.Turing.ListBlank.trim_mk, tier: T0, attempt: 5, spec: Encoding.lean)
theorem _root_.Turing.ListBlank.trim_mk {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] (l : List Γ) :
    (ListBlank.mk l).trim = l.rdropWhile (· == default) :=
  by
  simp [ListBlank.trim, ListBlank.mk]
