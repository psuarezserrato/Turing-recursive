-- Verified by gemma_loop.py (declaration: TuringRecursive.kPrimeEquivFin4_main, tier: T0, attempt: 2, spec: Equivalence.lean)
@[simp]
theorem kPrimeEquivFin4_main : kPrimeEquivFin4 .main = 0 :=
  by
  -- The definition of kPrimeEquivFin4 .main being 0 is standard for 
  -- the canonical encoding of the first element of the set.
  simp [kPrimeEquivFin4]
