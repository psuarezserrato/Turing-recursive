/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authors: Pablo Suárez-Serrato (November 2026)
-/
module

public import Mathlib.Computability.PartrecCode
public import TuringRecursive.Encoding
public import TuringRecursive.Eval
import Mathlib.Basic.Finite.Prod

/-!
# Computability and Kleene Normal Form of Fixed `TM0` Turing Machines

This file implements Milestone M3 (`T-A` and `T-A'`): every Post–Turing machine
`M : TM0.Machine Γ Λ` whose transition table is primitive recursive (and in particular every
machine over finite `Primcodable` alphabet `Γ` and state space `Λ`, without requiring
`[DecidableEq]`) has primitive recursive single-step transition `TM0.step M`, partial recursive
configuration and list evaluators, and a literal `Nat.Partrec.Code` normal form on
`Encodable.encode`d inputs:

* `Turing.TM0.step_primrec_of_primrec`: `Primrec₂ M → Primrec (TM0.step M)` over arbitrary
  `Primcodable` types `Γ` and `Λ`.
* `Turing.TM0.step_primrec`: `Primrec (TM0.step M)` for any `[Finite Γ] [Finite Λ]` (requiring no
  `DecidableEq` instances).
* `Turing.TM0.evalCfg_partrec`: `Partrec (StateTransition.eval (TM0.step M))` for finite `Γ`, `Λ`.
* `Turing.TM0.eval_partrec`: `Partrec (TM0.eval M)` for finite `Γ`, `Λ`.
* `Turing.TM0.exists_code_eval`: Kleene normal-form existence of `c : Nat.Partrec.Code` such that
  `∀ l, c.eval (Encodable.encode l) = (TM0.eval M l).map Encodable.encode`.
-/

open Turing

namespace TuringRecursive

@[expose] public section

/-! ## `TM0` Statement Equivalence and Step Helpers -/

/-- `stmtEquivSum` maps `TM0.Stmt.move d` to `Sum.inl d`. -/
-- tier: T0
@[simp]
theorem stmtEquivSum_move {Γ : Type*} (d : Dir) :
    stmtEquivSum (TM0.Stmt.move d : TM0.Stmt Γ) = Sum.inl d := by
  simp [stmtEquivSum]

/-- `stmtEquivSum` maps `TM0.Stmt.write a` to `Sum.inr a`. -/
-- tier: T0
@[simp]
theorem stmtEquivSum_write {Γ : Type*} (a : Γ) :
    stmtEquivSum (TM0.Stmt.write a) = Sum.inr a := by
  simp [stmtEquivSum]

/-- Single-step execution `TM0.step M c` halts (`= none`) if and only if the transition table
returns `none` at `(c.q, c.Tape.head)`. -/
-- tier: T0
@[simp]
theorem _root_.Turing.TM0.step_eq_none_iff {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (c : TM0.Cfg Γ Λ) :
    TM0.step M c = none ↔ M c.q c.Tape.head = none := by
  cases c
  simp [TM0.step]

/-- Executing a single `TM0.Stmt Γ` instruction (`move` or `write`) on a `Tape Γ` is binary
primitive recursive. -/
-- tier: T1
theorem primrec₂_stmtStep {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ fun (s : TM0.Stmt Γ) (T : Tape Γ) ↦
      match s with
      | TM0.Stmt.move d => T.move d
      | TM0.Stmt.write a => T.write a := by
  have hs : Primrec fun p : TM0.Stmt Γ × Tape Γ ↦ stmtEquivSum p.1 :=
    (Primrec.of_equiv (e := stmtEquivSum)).comp .fst
  refine (Primrec.sumCasesOn hs
    (Primrec.tape_move.comp .snd (Primrec.snd.comp .fst)).to₂
    (Primrec.tape_write.comp .snd (Primrec.snd.comp .fst)).to₂).to₂.of_eq fun s T ↦ ?_
  cases s <;> simp

/-- Initializing a `TM0` configuration from an input list (`TM0.init`) is primitive recursive. -/
-- tier: T1
theorem _root_.Turing.TM0.init_primrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ] :
    Primrec (TM0.init : List Γ → TM0.Cfg Γ Λ) :=
  Primrec.cfg_mk (.const default) Primrec.tape_mk₁

/-! ## `T-A` and `T-A'`: Fixed-Machine `TM0` Computability -/

/-- For any `TM0` machine `M` (finite or infinite) whose transition function is binary primitive
recursive, single-step execution `TM0.step M` is primitive recursive. -/
-- tier: T1
theorem _root_.Turing.TM0.step_primrec_of_primrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    {M : TM0.Machine Γ Λ} (hM : Primrec₂ M) :
    Primrec (TM0.step M) := by
  have hlookup : Primrec fun c : TM0.Cfg Γ Λ ↦ M c.q c.Tape.head :=
    hM.comp Primrec.cfg_q (Primrec.tape_head.comp Primrec.cfg_tape)
  have hnext : Primrec₂ fun (c : TM0.Cfg Γ Λ) (p : Λ × TM0.Stmt Γ) ↦
      (⟨p.1, match p.2 with
        | TM0.Stmt.move d => c.Tape.move d
        | TM0.Stmt.write a => c.Tape.write a⟩ : TM0.Cfg Γ Λ) :=
    (Primrec.cfg_mk (Primrec.fst.comp .snd)
      (primrec₂_stmtStep.comp (Primrec.snd.comp .snd) (Primrec.cfg_tape.comp .fst))).to₂
  refine (Primrec.option_map hlookup hnext).of_eq fun ⟨q, T⟩ ↦ ?_
  rcases h : M q T.head with _ | ⟨q', s⟩ <;> simp [TM0.step, h]
  cases s <;> rfl

/-- For any `TM0` machine `M` over finite `Primcodable` alphabet `Γ` and state type `Λ` (requiring
neither `[DecidableEq Γ]` nor `[DecidableEq Λ]`), `TM0.step M` is primitive recursive. -/
-- tier: T1
theorem _root_.Turing.TM0.step_primrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    Primrec (TM0.step M) :=
  TM0.step_primrec_of_primrec (Primrec₂.uncurry.mp (Primrec.dom_finite (Function.uncurry M)))

/-- Configuration-to-configuration evaluation `StateTransition.eval (TM0.step M)` of any finite
`TM0` machine `M` is partial recursive. -/
-- tier: T2
theorem _root_.Turing.TM0.evalCfg_partrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    Partrec (StateTransition.eval (TM0.step M)) :=
  StateTransition.eval_partrec (TM0.step_primrec M).to_comp

/-- Input-list to output-`ListBlank` evaluation `TM0.eval M` of any finite `TM0` machine `M` is
partial recursive. -/
-- tier: T2
theorem _root_.Turing.TM0.eval_partrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    Partrec (TM0.eval M) :=
  ((TM0.evalCfg_partrec M).comp TM0.init_primrec.to_comp).map
    (((Primrec.tape_right₀.comp Primrec.cfg_tape).comp .snd).to₂.to_comp)

/-- Literal Kleene normal-form corollary of `TM0.eval_partrec` on natural-number codes: every
finite `TM0` machine `M` is simulated on `Encodable.encode`d input lists by a concrete
`Nat.Partrec.Code`. -/
-- tier: T2
theorem _root_.Turing.TM0.exists_code_eval
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    ∃ c : Nat.Partrec.Code, ∀ l,
      c.eval (Encodable.encode l) = (TM0.eval M l).map Encodable.encode := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (TM0.eval_partrec M)
  refine ⟨c, fun l ↦ ?_⟩
  simpa [Encodable.encodek] using congrFun hc (Encodable.encode l)

end

end TuringRecursive
