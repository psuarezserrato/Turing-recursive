-- Verified by gemma_loop.py (declaration: TuringRecursive.TM0Code.machine_nil, tier: T0, attempt: 2, spec: Uniform.lean)
@[simp]
theorem TM0Code.machine_nil (q a : ℕ) :
    (⟨[]⟩ : TM0Code).machine q a = none :=
  by
  let m : TM0Code := ⟨[]⟩
  simp [TM0Code.machine]
