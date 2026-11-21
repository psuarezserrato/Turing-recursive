/-
Copyright (c) 2026 TuringRecursive contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TuringRecursive contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.DropRight

/-!
# Primitive Recursiveness of Right-End List Operations

This file proves generic primitive recursiveness results for right-end list operations from
`Mathlib.Data.List.DropRight` and `Init.Data.List`:

* `List.dropLast_eq_rdrop`: `l.dropLast = l.rdrop 1`.
* `Primrec.list_rdrop`: dropping `n` elements from the right end of a list is binary primitive
  recursive.
* `Primrec.list_rdropWhile`: stripping trailing elements satisfying a primitive recursive boolean
  predicate `p` is primitive recursive.
* `Primrec.list_dropLast`: dropping the last element of a list is primitive recursive.
-/

@[expose] public section

/-- Dropping the last element of a list coincides with `List.rdrop` of length `1`. -/
-- tier: T0
theorem _root_.List.dropLast_eq_rdrop {α : Type*} (l : List α) :
    l.dropLast = l.rdrop 1 :=
  l.dropLast_eq_take

/-- Dropping `n` elements from the right end of a list (`List.rdrop`) is binary primitive
recursive. -/
-- tier: T1
theorem _root_.Primrec.list_rdrop {α : Type*} [Primcodable α] :
    Primrec₂ (@List.rdrop α) :=
  (Primrec.list_take.comp (Primrec.nat_sub.comp (Primrec.list_length.comp .fst) .snd) .fst).to₂

/-- Stripping trailing elements satisfying a primitive recursive predicate `p` via
`List.rdropWhile` is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.list_rdropWhile {α : Type*} [Primcodable α] {p : α → Bool}
    (hp : Primrec p) : Primrec (List.rdropWhile p) :=
  Primrec.list_reverse.comp ((Primrec.list_dropWhile hp).comp Primrec.list_reverse)

/-- Dropping the last element of a list (`List.dropLast`) is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.list_dropLast {α : Type*} [Primcodable α] :
    Primrec (@List.dropLast α) :=
  (Primrec.list_rdrop.comp .id (.const 1)).of_eq fun l ↦ (List.dropLast_eq_rdrop l).symm

end
