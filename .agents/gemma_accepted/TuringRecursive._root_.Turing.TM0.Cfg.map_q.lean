-- Verified by gemma_loop.py (declaration: TuringRecursive._root_.Turing.TM0.Cfg.map_q, tier: T0, attempt: 4, spec: Uniform.lean)
@[simp]
theorem _root_.Turing.TM0.Cfg.map_q {Γ Γ' Λ Λ' : Type*} [Inhabited Γ] [Inhabited Γ']
    (f : PointedMap Γ Γ') (g : Λ → Λ') (c : TM0.Cfg Γ Λ) :
    (c.map f g).q = g c.q :=
  by
  simp [TM0.Cfg.map]
