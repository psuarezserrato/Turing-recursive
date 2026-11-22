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

public import TuringRecursive.TM0Eval

/-!
# Uniform `TM0Code` over `ℕ` and Pointed Relabeling

This file implements Milestone M4 (`T-C`): a concrete tabular code `TM0Code` for finite `TM0`
machines over state and tape alphabet `ℕ` (`blank = 0`, `init state = 0`), primitive recursive
uniform single-step execution, partial recursive uniform run-to-completion evaluation, and
universe-polymorphic injective pointed relabeling of arbitrary finite `TM0` machines into
`TM0Code`:

* `TM0Code`, `TM0Code.machine`, `tm0CodeEquivList`, `instPrimcodableTM0Code`: concrete 2D list
  representation of `TM0.Machine ℕ ℕ` (halting out of bounds) and its `Primcodable` instance.
* `decode_encode_tm0Code`: explicit `Encodable` round-trip theorem for `TM0Code`.
* `TM0Code.step_primrec`: uniform single-step execution `(m, c) ↦ TM0.step m.machine c` is
  `Primrec₂`.
* `TM0Code.eval_partrec`: uniform evaluation `(m, c) ↦ StateTransition.eval (TM0.step m.machine) c`
  is `Partrec₂`.
* `TM0Code.exists_relabeling`: every `M : TM0.Machine Γ Λ` over `[Finite Γ] [Finite Λ]` admits
  injective `f : PointedMap Γ ℕ`, `g : PointedMap Λ ℕ`, and `m : TM0Code` commuting with both
  `StateTransition.eval` and `TM0.eval`.
-/

open Turing

namespace TuringRecursive

@[expose] public section

/-! ## `TM0Code` Representation and `Primcodable` Instance -/

/-- Concrete tabular code for a finite `TM0` machine over state and symbol type `ℕ` (`blank = 0`,
`init state = 0`). Entry `table[q]?[a]?` stores `Option (ℕ × TM0.Stmt ℕ)`; out-of-bounds indices
halt (`none`), so every `TM0Code` denotes a total `TM0.Machine ℕ ℕ`. -/
structure TM0Code where
  /-- Underlying 2D transition table indexed by state `q` and tape symbol `a`. -/
  table : List (List (Option (ℕ × TM0.Stmt ℕ)))
  deriving DecidableEq, Inhabited

/-- The `TM0.Machine ℕ ℕ` denoted by `m : TM0Code`, halting (`none`) whenever state `q` or symbol
`a` falls outside `m.table`. -/
def TM0Code.machine (m : TM0Code) : TM0.Machine ℕ ℕ :=
  fun q a ↦ (m.table[q]?).bind fun row ↦ (row[a]?).join

/-- Explicit equivalence between `TM0Code` and its underlying transition table. -/
def tm0CodeEquivList : TM0Code ≃ List (List (Option (ℕ × TM0.Stmt ℕ))) where
  toFun m := m.table
  invFun t := ⟨t⟩
  left_inv m := by cases m; rfl
  right_inv _ := rfl

/-- `Primcodable` instance on `TM0Code` via `tm0CodeEquivList`. -/
instance instPrimcodableTM0Code : Primcodable TM0Code :=
  Primcodable.ofEquiv (List (List (Option (ℕ × TM0.Stmt ℕ)))) tm0CodeEquivList

/-- `tm0CodeEquivList` projects a `TM0Code` to its underlying transition table `m.table`. -/
-- tier: T0
@[simp]
theorem tm0CodeEquivList_apply (m : TM0Code) :
    tm0CodeEquivList m = m.table := by
  simp [tm0CodeEquivList]

/-- The inverse of `tm0CodeEquivList` wraps a 2D transition table into a `TM0Code`. -/
-- tier: T0
@[simp]
theorem tm0CodeEquivList_symm_apply (t : List (List (Option (ℕ × TM0.Stmt ℕ)))) :
    tm0CodeEquivList.symm t = ⟨t⟩ := by
  simp [tm0CodeEquivList]

/-- Decoding an encoded `TM0Code` recovers the original machine code. -/
-- tier: T0
theorem decode_encode_tm0Code (m : TM0Code) :
    Encodable.decode (Encodable.encode m) = some m :=
  Encodable.encodek m

/-- The empty transition table `⟨[]⟩` halts (`none`) on every state `q` and symbol `a`. -/
-- tier: T0
@[simp]
theorem TM0Code.machine_nil (q a : ℕ) :
    (⟨[]⟩ : TM0Code).machine q a = none := by
  simp [TM0Code.machine]

/-- Looking up a state index `q` beyond `m.table.length` in `m.machine` halts (`none`). -/
-- tier: T0
theorem TM0Code.machine_eq_none_of_length_le (m : TM0Code) {q : ℕ} (hq : m.table.length ≤ q)
    (a : ℕ) : m.machine q a = none := by
  simp [TM0Code.machine, List.getElem?_eq_none hq]

/-- Mapping a `Tape` by a `PointedMap` commutes with `Tape.right₀`. -/
-- tier: T0
@[simp]
theorem _root_.Turing.Tape.map_right₀ {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']
    (f : PointedMap Γ Γ') (T : Tape Γ) :
    (T.map f).right₀ = T.right₀.map f := by
  ext i
  simp [Tape.map, Tape.right₀]

/-- Mapping a `TM0` configuration transforms its state `q` by `g`. -/
-- tier: T0
@[simp]
theorem _root_.Turing.TM0.Cfg.map_q {Γ Γ' Λ Λ' : Type*} [Inhabited Γ] [Inhabited Γ']
    (f : PointedMap Γ Γ') (g : Λ → Λ') (c : TM0.Cfg Γ Λ) :
    (c.map f g).q = g c.q := by
  simp [TM0.Cfg.map]

/-- Mapping a `TM0` configuration transforms its `Tape` by `Tape.map f`. -/
-- tier: T0
@[simp]
theorem _root_.Turing.TM0.Cfg.map_tape {Γ Γ' Λ Λ' : Type*} [Inhabited Γ] [Inhabited Γ']
    (f : PointedMap Γ Γ') (g : Λ → Λ') (c : TM0.Cfg Γ Λ) :
    (c.map f g).Tape = c.Tape.map f := by
  simp [TM0.Cfg.map]

/-! ## Uniform Computability of `TM0Code` -/

/-- Extracting the transition table `TM0Code.table` is primitive recursive. -/
-- tier: T1
theorem TM0Code.table_primrec :
    Primrec (TM0Code.table : TM0Code → List (List (Option (ℕ × TM0.Stmt ℕ)))) :=
  Primrec.of_equiv (e := tm0CodeEquivList)

/-- Uniform lookup `(m, q, a) ↦ m.machine q a` in a `TM0Code` transition table is primitive
recursive. -/
-- tier: T1
theorem TM0Code.machine_primrec :
    Primrec fun p : TM0Code × ℕ × ℕ ↦ p.1.machine p.2.1 p.2.2 := by
  have hrow : Primrec fun p : TM0Code × ℕ × ℕ ↦ p.1.table[p.2.1]? :=
    Primrec.list_getElem?.comp (TM0Code.table_primrec.comp .fst) (Primrec.fst.comp .snd)
  have hcell : Primrec₂ fun (p : TM0Code × ℕ × ℕ) (row : List (Option (ℕ × TM0.Stmt ℕ))) ↦
      row[p.2.2]? :=
    (Primrec.list_getElem?.comp .snd (Primrec.snd.comp (Primrec.snd.comp .fst))).to₂
  have hjoin : Primrec₂ fun (p : TM0Code × ℕ × ℕ) (row : List (Option (ℕ × TM0.Stmt ℕ))) ↦
      (row[p.2.2]?).join :=
    (Primrec.option_casesOn hcell (.const none) Primrec.snd.to₂).to₂.of_eq fun p row ↦ by
      dsimp only
      cases row[p.2.2]? <;> rfl
  exact Primrec.option_bind hrow hjoin

/-- Uniform single-step execution `(m, c) ↦ TM0.step m.machine c` is binary primitive recursive. -/
-- tier: T1
theorem TM0Code.step_primrec :
    Primrec₂ fun (m : TM0Code) (c : TM0.Cfg ℕ ℕ) ↦ TM0.step m.machine c := by
  have hlookup : Primrec fun p : TM0Code × TM0.Cfg ℕ ℕ ↦ p.1.machine p.2.q p.2.Tape.head :=
    TM0Code.machine_primrec.comp
      (Primrec.fst.pair ((Primrec.cfg_q.comp .snd).pair
        ((Primrec.tape_head.comp Primrec.cfg_tape).comp .snd)))
  refine (Primrec.option_map hlookup
    (Primrec.cfg_mk (Primrec.fst.comp .snd)
      (primrec₂_stmtStep.comp (Primrec.snd.comp .snd)
        (Primrec.cfg_tape.comp (Primrec.snd.comp .fst)))).to₂).to₂.of_eq fun m ⟨q, T⟩ ↦ ?_
  rcases h : m.machine q T.head with _ | ⟨q', s⟩ <;> simp [TM0.step, h]
  cases s <;> rfl

/-- Uniform evaluation `(m, c) ↦ StateTransition.eval (TM0.step m.machine) c` is binary partial
recursive. -/
-- tier: T2
theorem TM0Code.eval_partrec :
    Partrec₂ fun (m : TM0Code) (c : TM0.Cfg ℕ ℕ) ↦
      StateTransition.eval (TM0.step m.machine) c :=
  StateTransition.eval_partrec₂ (f := fun m : TM0Code ↦ TM0.step m.machine)
    TM0Code.step_primrec.to_comp

/-! ## Pointed Relabeling of Arbitrary Finite `TM0` Machines -/

/-- Construct a `TM0Code` from a finite `Fin nΛ × Fin nΓ` transition function via nested
`List.ofFn`. -/
def TM0Code.ofFin {nΛ nΓ : ℕ} (F : Fin nΛ → Fin nΓ → Option (ℕ × TM0.Stmt ℕ)) : TM0Code :=
  ⟨List.ofFn fun i ↦ List.ofFn fun j ↦ F i j⟩

/-- Looking up in-bounds indices `(i.1, j.1)` in `(TM0Code.ofFin F).machine` returns `F i j`. -/
-- tier: T1
@[simp]
theorem TM0Code.machine_ofFin {nΛ nΓ : ℕ}
    (F : Fin nΛ → Fin nΓ → Option (ℕ × TM0.Stmt ℕ)) (i : Fin nΛ) (j : Fin nΓ) :
    (TM0Code.ofFin F).machine i.1 j.1 = F i j := by
  simp [TM0Code.ofFin, TM0Code.machine]

/-- If `M'` agrees with `M` along `g` and `f` on every state-symbol pair `(q, a)`, then `TM0.step`
commutes with `TM0.Cfg.map f g` on all configurations. -/
-- tier: T1
theorem _root_.Turing.TM0.step_map_of_machine_eq
    {Γ Γ' Λ Λ' : Type*} [Inhabited Γ] [Inhabited Γ'] [Inhabited Λ] [Inhabited Λ']
    {M : TM0.Machine Γ Λ} {M' : TM0.Machine Γ' Λ'} (f : PointedMap Γ Γ') (g : Λ → Λ')
    (hM : ∀ q a, M' (g q) (f a) = (M q a).map (Prod.map g (TM0.Stmt.map f)))
    (c : TM0.Cfg Γ Λ) :
    TM0.step M' (c.map f g) = (TM0.step M c).map (TM0.Cfg.map f g) := by
  rcases c with ⟨q, T⟩
  simp only [TM0.step, TM0.Cfg.map, Tape.map_fst, hM q T.1]
  rcases M q T.1 with _ | ⟨q', d | a⟩
  · rfl
  · simp [TM0.Stmt.map, TM0.Cfg.map, Tape.map_move]
  · simp [TM0.Stmt.map, TM0.Cfg.map]

/-- Universe-polymorphic `StateTransition.eval` commutation when `tr : σ₁ → σ₂` intertwines `f₁`
and `f₂` in lockstep (`∀ s, f₂ (tr s) = (f₁ s).map tr`). -/
-- tier: T2
theorem _root_.StateTransition.eval_map_of_step_eq {σ₁ σ₂ : Type*}
    {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} (tr : σ₁ → σ₂)
    (hstep : ∀ s, f₂ (tr s) = (f₁ s).map tr) (s : σ₁) :
    StateTransition.eval f₂ (tr s) = (StateTransition.eval f₁ s).map tr := by
  have H : StateTransition.Respects f₁ f₂ fun a b ↦ tr a = b := by
    refine StateTransition.fun_respects.2 fun a ↦ ?_
    cases h : f₁ a with
    | none => simp [StateTransition.FRespects, hstep, h]
    | some b =>
      refine Relation.TransGen.single ?_
      simp [hstep, h]
  refine Part.ext fun b₂ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨b₁, rfl, hb₁⟩ := StateTransition.tr_eval_rev H rfl h
    exact (Part.mem_map_iff _).2 ⟨b₁, hb₁, rfl⟩
  · obtain ⟨b₁, hb₁, rfl⟩ := (Part.mem_map_iff _).1 h
    obtain ⟨_, rfl, hb₂⟩ := StateTransition.tr_eval H rfl hb₁
    exact hb₂

/-- Every finite inhabited type `α` admits an equivalence `e : α ≃ Fin n` sending `default` to an
element with underlying value `0`. -/
-- tier: T2
theorem exists_fin_equiv_map_default {α : Type*} [Inhabited α] [Finite α] :
    ∃ (n : ℕ) (e : α ≃ Fin n), (e default).1 = 0 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  let z : Fin n := ⟨0, Nat.zero_lt_of_lt (e default).isLt⟩
  refine ⟨n, e.trans (Equiv.swap (e default) z), ?_⟩
  simp [z]

/-- Every `TM0` machine `M` over finite `Γ` and `Λ` admits injective pointed relabelings
`f : PointedMap Γ ℕ` and `g : PointedMap Λ ℕ` together with a `TM0Code` `m` simulating `M` both on
arbitrary configurations (`StateTransition.eval`) and on input lists (`TM0.eval`). -/
-- tier: T2
theorem TM0Code.exists_relabeling
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Finite Γ] [Finite Λ]
    (M : TM0.Machine Γ Λ) :
    ∃ (f : PointedMap Γ ℕ) (g : PointedMap Λ ℕ) (m : TM0Code),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ c : TM0.Cfg Γ Λ,
        StateTransition.eval (TM0.step m.machine) (c.map f g) =
          (StateTransition.eval (TM0.step M) c).map (TM0.Cfg.map f g)) ∧
      (∀ l : List Γ,
        TM0.eval m.machine (l.map f) = (TM0.eval M l).map (ListBlank.map f)) := by
  obtain ⟨nΓ, eΓ, heΓ⟩ := exists_fin_equiv_map_default (α := Γ)
  obtain ⟨nΛ, eΛ, heΛ⟩ := exists_fin_equiv_map_default (α := Λ)
  let f : PointedMap Γ ℕ := ⟨fun a ↦ (eΓ a).1, heΓ⟩
  let g : PointedMap Λ ℕ := ⟨fun q ↦ (eΛ q).1, heΛ⟩
  let m : TM0Code := TM0Code.ofFin fun i j ↦
    (M (eΛ.symm i) (eΓ.symm j)).map (Prod.map g (TM0.Stmt.map f))
  have hm : ∀ q a, m.machine (g q) (f a) = (M q a).map (Prod.map g (TM0.Stmt.map f)) :=
    fun q a ↦ by simp [m, f, g]
  have hstep : ∀ c : TM0.Cfg Γ Λ,
      TM0.step m.machine (c.map f g) = (TM0.step M c).map (TM0.Cfg.map f g) :=
    TM0.step_map_of_machine_eq f g hm
  have hevalCfg : ∀ c : TM0.Cfg Γ Λ,
      StateTransition.eval (TM0.step m.machine) (c.map f g) =
        (StateTransition.eval (TM0.step M) c).map (TM0.Cfg.map f g) :=
    StateTransition.eval_map_of_step_eq (TM0.Cfg.map f g) hstep
  refine ⟨f, g, m, Fin.val_injective.comp eΓ.injective, Fin.val_injective.comp eΛ.injective,
    hevalCfg, fun l ↦ ?_⟩
  simp only [TM0.eval, ← TM0.map_init f g l, hevalCfg, Part.map_map]
  congr 1
  funext c
  simp

end

end TuringRecursive
