-- Verified by gemma_loop.py (declaration: TuringRecursive._root_.Turing.TM0.Cfg.map_tape, tier: T0, attempt: 1, spec: Uniform.lean)
@[simp]
theorem _root_.Turing.TM0.Cfg.map_tape {Γ Γ' Λ Λ' : Type*} [Inhabited Γ] [Inhabited Γ']
    (f : PointedMap Γ Γ') (g : Λ → Λ') (c : TM0.Cfg Γ Λ) :
    (c.map f g).Tape = c.Tape.map f :=
  by
  simp [TM0.Cfg.map]
