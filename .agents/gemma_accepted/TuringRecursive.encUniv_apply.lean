-- Verified by gemma_loop.py (declaration: TuringRecursive.encUniv_apply, tier: T0, attempt: 1, spec: Universal.lean)
theorem encUniv_apply (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    encUniv (m, c) = encNat (Encodable.encode (m, c)) :=
  by
  rewrite [encUniv]
  rfl
