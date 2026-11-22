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

public import Mathlib.Computability.Partrec
public import Mathlib.Computability.StateTransition

/-!
# Computability and Iteration of Deterministic State Transition Systems

This file proves Milestone `T-B` for generic deterministic state transition systems
`f : σ → Option σ` (`StateTransition.eval` and `StateTransition.Reaches`):

* `StateTransition.eval_partrec`: if `σ` is `Primcodable` and `f : σ → Option σ` is `Computable`,
  then running `f` to completion (`StateTransition.eval f`) is partial recursive (`Partrec`).
* `StateTransition.eval_partrec₂`: parameterized version showing that
  `(a, s) ↦ StateTransition.eval (f a) s` is `Partrec₂` whenever `f : α → σ → Option σ` is
  `Computable₂`.
* `StateTransition.reaches_iff_exists_iterate`: reachability `StateTransition.Reaches f a b` is
  equivalent to `∃ n : ℕ, (flip Option.bind f)^[n] (some a) = some b`.
-/

@[expose] public section

open Relation

/-- Applying the Kleisli-lifted step operator `flip Option.bind f` to `none` yields `none`. -/
-- tier: T0
@[simp]
theorem StateTransition.flip_bind_none {σ : Type*} (f : σ → Option σ) :
    flip Option.bind f none = none := by
  simp [flip]

/-- Applying the Kleisli-lifted step operator `flip Option.bind f` to `some a` yields `f a`. -/
-- tier: T0
@[simp]
theorem StateTransition.flip_bind_some {σ : Type*} (f : σ → Option σ) (a : σ) :
    flip Option.bind f (some a) = f a := by
  simp [flip]

/-- Iterating `flip Option.bind f` any number of times starting from `none` stays at `none`. -/
-- tier: T0
@[simp]
theorem StateTransition.iterate_flip_bind_none {σ : Type*} (f : σ → Option σ) (n : ℕ) :
    (flip Option.bind f)^[n] none = none :=
  Function.iterate_fixed (StateTransition.flip_bind_none f) n

/-- Converting a computable transition function `f : σ → Option σ` into the sum-valued step map
`s ↦ (f s).elim (Sum.inl s) Sum.inr` consumed by `PFun.fix` is computable. -/
-- tier: T1
theorem StateTransition.computable_stepSum {σ : Type*} [Primcodable σ] {f : σ → Option σ}
    (hf : Computable f) : Computable fun s ↦ (f s).elim (Sum.inl s) Sum.inr :=
  (Computable.option_casesOn hf Computable.sumInl
    (Computable.sumInr.comp Computable.snd).to₂).of_eq fun s ↦ by cases f s <;> rfl

/-- Lifting a binary computable family of transition functions `f : α → σ → Option σ` to the
product state space `α × σ` via `p ↦ (f p.1 p.2).map (p.1, ·)` is computable. -/
-- tier: T1
theorem StateTransition.computable_prodStep {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → σ → Option σ} (hf : Computable₂ f) :
    Computable fun p : α × σ ↦ (f p.1 p.2).map (p.1, ·) :=
  Computable.option_map hf ((Computable.fst.comp Computable.fst).pair Computable.snd).to₂

/-- For a fixed parameter `a : α`, the embedding `s ↦ (a, s)` is a `StateTransition.Respects`
simulation from `f a` into the product transition `p ↦ (f p.1 p.2).map (p.1, ·)`. -/
-- tier: T1
theorem StateTransition.respects_prodStep {α σ : Type*} (f : α → σ → Option σ) (a : α) :
    StateTransition.Respects (f a) (fun p : α × σ ↦ (f p.1 p.2).map (p.1, ·))
      fun s p ↦ (a, s) = p := by
  refine StateTransition.fun_respects.2 fun s ↦ ?_
  cases h : f a s with
  | none => simp [StateTransition.FRespects, h]
  | some _ => exact TransGen.single (by simp [h])

/-- Running a computable deterministic state transition system `f : σ → Option σ` to completion
(`StateTransition.eval f`) is partial recursive. -/
-- tier: T2
theorem _root_.StateTransition.eval_partrec {σ : Type*} [Primcodable σ] {f : σ → Option σ}
    (hf : Computable f) : Partrec (StateTransition.eval f) :=
  (Partrec.fix (StateTransition.computable_stepSum hf).partrec).of_eq fun _ ↦ rfl

/-- Evaluating the product transition `p ↦ (f p.1 p.2).map (p.1, ·)` from `(a, s)` equals
mapping `(a, ·)` over `StateTransition.eval (f a) s` (universe-polymorphic across `α` and `σ`). -/
-- tier: T2
theorem StateTransition.eval_prodStep {α σ : Type*} (f : α → σ → Option σ) (a : α) (s : σ) :
    StateTransition.eval (fun p : α × σ ↦ (f p.1 p.2).map (p.1, ·)) (a, s) =
      (StateTransition.eval (f a) s).map (a, ·) := by
  have H := StateTransition.respects_prodStep f a
  refine Part.ext fun p ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨s', hs', hp⟩ := StateTransition.tr_eval_rev H rfl h
    exact (Part.mem_map_iff _).2 ⟨s', hp, hs'⟩
  · obtain ⟨s', hs', hp⟩ := (Part.mem_map_iff _).1 h
    obtain ⟨_, rfl, hev⟩ := StateTransition.tr_eval H rfl hs'
    rwa [hp] at hev

/-- Parameterized version of `StateTransition.eval_partrec`: evaluating a uniformly computable
family of transition functions `f : α → σ → Option σ` is binary partial recursive. -/
-- tier: T2
theorem _root_.StateTransition.eval_partrec₂ {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → σ → Option σ} (hf : Computable₂ f) :
    Partrec₂ fun a ↦ StateTransition.eval (f a) := by
  have hprod : Partrec (StateTransition.eval fun p : α × σ ↦ (f p.1 p.2).map (p.1, ·)) :=
    StateTransition.eval_partrec (StateTransition.computable_prodStep hf)
  refine (hprod.map (Computable.snd.comp Computable.snd).to₂).of_eq ?_
  rintro ⟨a, s⟩
  exact Part.ext fun x ↦ by simp [StateTransition.eval_prodStep]

/-- Reachability in a deterministic state transition system `f : σ → Option σ` is equivalent to
iterating `flip Option.bind f` finitely many times from `some a`. -/
-- tier: T2
theorem _root_.StateTransition.reaches_iff_exists_iterate {σ : Type*} {f : σ → Option σ}
    {a b : σ} :
    StateTransition.Reaches f a b ↔ ∃ n : ℕ, (flip Option.bind f)^[n] (some a) = some b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply', hn, StateTransition.flip_bind_some]
      exact Option.mem_def.1 hbc
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hn
      exact hn ▸ ReflTransGen.refl
    | succ n ih =>
      rw [Function.iterate_succ_apply, StateTransition.flip_bind_some] at hn
      cases hfa : f a with
      | none =>
        rw [hfa, StateTransition.iterate_flip_bind_none] at hn
        cases hn
      | some a' =>
        rw [hfa] at hn
        exact ReflTransGen.head (Option.mem_def.2 hfa) (ih hn)

end
