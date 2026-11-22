-- Verified by gemma_loop.py (declaration: TuringRecursive.decUniv_apply, tier: T0, attempt: 1, spec: Universal.lean)
theorem decUniv_apply (L : ListBlank Γ₀) :
    decUniv L = (Encodable.decode (decNat L)).getD default :=
  by
  rw [decUniv]
