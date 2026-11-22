-- Verified by gemma_loop.py (declaration: TuringRecursive._root_.Turing.Tape.map_right₀, tier: T0, attempt: 5, spec: Uniform.lean)
@[simp]
theorem _root_.Turing.Tape.map_right₀ {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']
    (f : PointedMap Γ Γ') (T : Tape Γ) :
    (T.map f).right₀ = T.right₀.map f :=
  by
  ext i
  simp [Tape.map, Tape.right₀]
