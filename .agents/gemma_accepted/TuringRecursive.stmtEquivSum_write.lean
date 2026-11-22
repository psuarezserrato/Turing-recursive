-- Verified by gemma_loop.py (declaration: TuringRecursive.stmtEquivSum_write, tier: T0, attempt: 1, spec: TM0Eval.lean)
@[simp]
theorem stmtEquivSum_write {Γ : Type*} (a : Γ) :
    stmtEquivSum (TM0.Stmt.write a) = Sum.inr a :=
  by
  simp [stmtEquivSum]
