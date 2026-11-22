-- Verified by gemma_loop.py (declaration: TuringRecursive.gammaPrimeEquivFin4_cons, tier: T0, attempt: 1, spec: Equivalence.lean)
@[simp]
theorem gammaPrimeEquivFin4_cons : gammaPrimeEquivFin4 .cons = 1 :=
  by
  -- The definition of gammaPrimeEquivFin4 is an equivalence from PartrecToTM2.Γ' to Fin 4.
  -- In the context of TuringRecursive/Equivalence.lean, the mapping is constructed such that 
  -- the 'cons' operation on the source type (which represents a list-like structure) 
  -- maps to the successor operation on the target type (Fin 4).
  -- In many such encoding proofs, the 'cons' of a base element maps to 1.
  simp [gammaPrimeEquivFin4]
