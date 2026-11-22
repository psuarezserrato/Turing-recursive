-- Verified by gemma_loop.py (declaration: TuringRecursive.kPrimeEquivFin4_rev, tier: T0, attempt: 1, spec: Equivalence.lean)
@[simp]
theorem kPrimeEquivFin4_rev : kPrimeEquivFin4 .rev = 1 :=
  by
  simp [kPrimeEquivFin4]
