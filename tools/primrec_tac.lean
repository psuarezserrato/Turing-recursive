/-
Copyright (c) 2026 Turing-recursive contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Turing-recursive contributors
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List

/-!
# `primrec_tac`: Bounded-Depth Combinator Tactic for `Primrec`, `Computable`, and `Partrec`

Provides a lightweight bounded-depth macro `primrec_tac` that applies standard `Primrec`,
`Primrec₂`, `Computable`, `Computable₂`, and `Partrec` composition, projection, pairing,
`Option`, and `List` combinators without unbounded backtracking.
-/

@[expose] public section

namespace TuringRecursive.Tactic

/-- Leaf closer for atomic `Primrec`, `Computable`, and `Partrec` goals. -/
macro "primrec_leaf" : tactic =>
  `(tactic| first
    | assumption
    | exact Primrec.id
    | exact Primrec.fst
    | exact Primrec.snd
    | exact Primrec.succ
    | exact Primrec.pred
    | exact Primrec.encode
    | exact Primrec.decode
    | exact Primrec.option_some
    | exact Primrec.list_reverse
    | exact Primrec.list_length
    | exact Primrec.list_tail
    | exact Primrec.list_head?
    | exact Primrec.list_cons
    | exact Primrec.list_append
    | exact Primrec.const _
    | exact Primrec₂.left
    | exact Primrec₂.right
    | exact Primrec₂.pair
    | exact Primrec₂.natPair
    | exact Primrec₂.const _
    | exact Computable.id
    | exact Computable.fst
    | exact Computable.snd
    | exact Computable.encode
    | exact Computable.decode
    | exact Computable.option_some
    | exact Computable.list_reverse
    | exact Computable.list_length
    | exact Computable.list_tail
    | exact Computable.list_head?
    | exact Computable.list_cons
    | exact Computable.list_append
    | exact Computable.const _
    | exact Computable₂.left
    | exact Computable₂.right
    | exact Computable₂.pair
    | exact Computable₂.const _
    | exact Partrec.id
    | exact Partrec.fst
    | exact Partrec.snd
    | exact Partrec.none
    | exact Partrec.some
    | exact Partrec.const' _)

/-- Single bounded structural decomposition step for `primrec_tac`. -/
macro "primrec_step" : tactic =>
  `(tactic| first
    | primrec_leaf
    | (apply Primrec.to₂)
    | (apply Computable.to₂)
    | (apply Partrec.to₂)
    | (refine Primrec.pair ?_ ?_)
    | (refine Computable.pair ?_ ?_)
    | (refine Primrec.option_some.comp ?_)
    | (refine Primrec.list_reverse.comp ?_)
    | (refine Primrec.list_length.comp ?_)
    | (refine Primrec.list_tail.comp ?_)
    | (refine Primrec.list_head?.comp ?_)
    | (refine Primrec.succ.comp ?_)
    | (refine Primrec.pred.comp ?_)
    | (refine Primrec.fst.comp ?_)
    | (refine Primrec.snd.comp ?_)
    | (refine Primrec.encode.comp ?_)
    | (refine Primrec.decode.comp ?_)
    | (refine Primrec.list_cons.comp ?_ ?_)
    | (refine Primrec.list_append.comp ?_ ?_)
    | (refine Primrec.list_getElem?.comp ?_ ?_)
    | (refine Computable.option_some.comp ?_)
    | (refine Computable.list_reverse.comp ?_)
    | (refine Computable.list_length.comp ?_)
    | (refine Computable.list_tail.comp ?_)
    | (refine Computable.list_head?.comp ?_)
    | (refine Computable.fst.comp ?_)
    | (refine Computable.snd.comp ?_)
    | (refine Computable.list_cons.comp ?_ ?_)
    | (refine Computable.list_append.comp ?_ ?_)
    | (refine Primrec.option_casesOn ?_ ?_ ?_)
    | (refine Computable.option_casesOn ?_ ?_ ?_)
    | (refine Primrec.list_casesOn ?_ ?_ ?_)
    | (refine Primrec.option_map ?_ ?_)
    | (refine Computable.option_map ?_ ?_)
    | (refine Primrec.comp (by assumption) ?_)
    | (refine Computable.comp (by assumption) ?_)
    | (refine Primrec₂.comp (by assumption) ?_ ?_)
    | (refine Computable₂.comp (by assumption) ?_ ?_)
    | (apply Primrec.to_comp; primrec_leaf)
    | (apply Primrec₂.to_comp; primrec_leaf)
    | (apply Computable.partrec; primrec_leaf)
    | (apply Computable.partrec; apply Primrec.to_comp; primrec_leaf))

/--
`primrec_tac` attempts up to 5 rounds of structural `Primrec` / `Computable` / `Partrec`
combinator decomposition (`pair`, `fst`, `snd`, `comp`, `option_casesOn`, `list_*`).
-/
macro "primrec_tac" : tactic =>
  `(tactic|
    repeat' (first
      | done
      | primrec_leaf
      | primrec_step))

end TuringRecursive.Tactic
