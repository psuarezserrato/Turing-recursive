-- Verified by gemma_loop.py (declaration: StateTransition.flip_bind_some, tier: T0, attempt: 2, spec: Eval.lean)
@[simp]
theorem StateTransition.flip_bind_some {σ : Type*} (f : σ → Option σ) (a : σ) :
    flip Option.bind f (some a) = f a :=
  by
  simp [flip]
