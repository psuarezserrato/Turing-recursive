-- Verified by gemma_loop.py (declaration: TuringRecursive.cfgEquivProd_apply, tier: T0, attempt: 1, spec: Encoding.lean)
@[simp]
theorem cfgEquivProd_apply {Γ Λ : Type*} [Inhabited Γ] (c : TM0.Cfg Γ Λ) :
    cfgEquivProd c = (c.q, c.Tape) :=
  by
  simp [cfgEquivProd]
