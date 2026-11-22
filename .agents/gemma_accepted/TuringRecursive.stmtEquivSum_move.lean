-- Verified by gemma_loop.py (declaration: TuringRecursive.stmtEquivSum_move, tier: T0, attempt: 2, spec: TM0Eval.lean)
@[simp]
theorem stmtEquivSum_move {Γ : Type*} (d : Dir) :
    stmtEquivSum (TM0.Stmt.move d : TM0.Stmt Γ) = Sum.inl d :=
  by
  simp [stmtEquivSum]
