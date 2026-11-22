-- Verified by gemma_loop.py (declaration: StateTransition.flip_bind_none, tier: T0, attempt: 2, spec: Eval.lean)
@[simp]
theorem StateTransition.flip_bind_none {σ : Type*} (f : σ → Option σ) :
    flip Option.bind f none = none :=
  by
  simp [flip]
