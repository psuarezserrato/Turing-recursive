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

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import TuringRecursive.ListPrimrec

/-!
# Gödel Encodings and Primitive Recursive Operations for Turing Machine Types

This file implements Milestone `E`: canonical blank-free representatives (`ListBlank.trim`),
diamond-free scoped `Primcodable` instances, round-trip lemmas, and primitive recursiveness of all
core operations on Mathlib's `Turing.Dir`, `Turing.TM0.Stmt`, `Turing.ListBlank`, `Turing.Tape`,
and `Turing.TM0.Cfg`:

* `Turing.ListBlank.trim`: canonical trailing-blank-free list representative of `L : ListBlank Γ`,
  together with `trim_mk`, `mk_trim`, `trim_injective`, `trim_congr`, and `rdropWhile_trim`.
* `instPrimcodableDir`, `instDecidableEqStmt`, `instPrimcodableStmt`, `instPrimcodableListBlank`,
  `instPrimcodableTape`, `instPrimcodableCfg`: scoped `Primcodable` (and `DecidableEq`) instances
  built via explicit equivalences (`Primcodable.ofEquiv`), requiring no `[DecidableEq Γ]` on
  `instPrimcodableListBlank`.
* `Primrec.listBlank_*` and `Primrec.tape_*`: primitive recursiveness of `mk`, `trim`, `head`,
  `tail`, `cons`, `nth` on `ListBlank Γ` and `move`, `write`, `mk₁`, `mk₂`, `nth`, `right₀` on
  `Tape Γ`.
* `decode_encode_*`: explicit `Encodable.decode (Encodable.encode x) = some x` round-trip theorems.
-/

@[expose] public section

open Turing

namespace TuringRecursive

/-! ## Canonical Representatives of `ListBlank` -/

/-- Canonical blank-free representative of a `ListBlank Γ` quotient element, obtained by stripping
all trailing `default` (blank) symbols via `List.rdropWhile (· == default)`. -/
-- tier: T2
def _root_.Turing.ListBlank.trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (L : ListBlank Γ) : List Γ :=
  L.liftOn (List.rdropWhile (· == default)) <| by
    rintro l _ ⟨n, rfl⟩
    induction n with
    | zero => simp
    | succ n ih =>
      simp [List.replicate_succ', ← List.append_assoc, ih]

/-- Computing `ListBlank.trim` on a quotient representative `ListBlank.mk l` strips trailing
`default` symbols via `List.rdropWhile`. -/
-- tier: T0
theorem _root_.Turing.ListBlank.trim_mk {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] (l : List Γ) :
    (ListBlank.mk l).trim = l.rdropWhile (· == default) := by
  simp [ListBlank.trim, ListBlank.mk]

/-- Re-quotienting the canonical representative `L.trim` recovers `L`. -/
-- tier: T2
theorem _root_.Turing.ListBlank.mk_trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (L : ListBlank Γ) : ListBlank.mk L.trim = L := by
  refine L.induction_on fun l ↦ Quotient.sound' (Or.inl ⟨(l.rtakeWhile (· == default)).length, ?_⟩)
  have hrep : l.rtakeWhile (· == default) =
      List.replicate (l.rtakeWhile (· == default)).length default :=
    List.eq_replicate_length.mpr fun _ hx ↦
      beq_iff_eq.mp (List.mem_rtakeWhile_imp (p := (· == default)) hx)
  exact List.rdropWhile_append_rtakeWhile.symm.trans
    (congrArg ((ListBlank.mk l).trim ++ ·) hrep)

/-- The canonical representative map `ListBlank.trim` is injective. -/
-- tier: T0
theorem _root_.Turing.ListBlank.trim_injective {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] :
    Function.Injective (@ListBlank.trim Γ _ _) :=
  Function.LeftInverse.injective ListBlank.mk_trim

/-- `ListBlank.trim` does not depend on the choice of `DecidableEq Γ` instance. -/
-- tier: T2
theorem _root_.Turing.ListBlank.trim_congr {Γ : Type*} [Inhabited Γ]
    (inst₁ inst₂ : DecidableEq Γ) (L : ListBlank Γ) :
    @ListBlank.trim Γ _ inst₁ L = @ListBlank.trim Γ _ inst₂ L :=
  Subsingleton.elim inst₁ inst₂ ▸ rfl

/-- `ListBlank.trim L` is fixed under `List.rdropWhile (· == default)`. -/
-- tier: T0
theorem _root_.Turing.ListBlank.rdropWhile_trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (L : ListBlank Γ) : L.trim.rdropWhile (· == default) = L.trim :=
  L.induction_on fun l ↦ List.rdropWhile_idempotent _ l

/-- The canonical trailing-blank-free list predicate is primitive recursive. -/
-- tier: T1
theorem listBlank_canonical_primrecPred {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [Primcodable Γ] :
    PrimrecPred fun l : List Γ ↦ l.rdropWhile (· == default) = l :=
  Primrec.eq.comp (Primrec.list_rdropWhile (Primrec.beq.comp .id (.const default))) .id

/-! ## Equivalences and Scoped `Primcodable` Instances -/

/-- Explicit equivalence between `Turing.Dir` and `Bool`. -/
def dirEquivBool : Dir ≃ Bool where
  toFun
    | .left => false
    | .right => true
  invFun
    | false => .left
    | true => .right
  left_inv d := by cases d <;> rfl
  right_inv b := by cases b <;> rfl

/-- Scoped `Primcodable` instance on `Turing.Dir` via `Dir ≃ Bool`. -/
scoped instance instPrimcodableDir : Primcodable Dir :=
  Primcodable.ofEquiv Bool dirEquivBool

/-- `dirEquivBool` maps `Dir.left` to `false`. -/
-- tier: T0
@[simp]
theorem dirEquivBool_left : dirEquivBool .left = false := by
  simp [dirEquivBool]

/-- `dirEquivBool` maps `Dir.right` to `true`. -/
-- tier: T0
@[simp]
theorem dirEquivBool_right : dirEquivBool .right = true := by
  simp [dirEquivBool]

/-- Explicit equivalence between `Turing.TM0.Stmt Γ` and `Dir ⊕ Γ`. -/
def stmtEquivSum {Γ : Type*} : TM0.Stmt Γ ≃ Dir ⊕ Γ where
  toFun
    | .move d => Sum.inl d
    | .write a => Sum.inr a
  invFun
    | Sum.inl d => .move d
    | Sum.inr a => .write a
  left_inv s := by cases s <;> rfl
  right_inv x := by cases x <;> rfl

/-- Scoped `DecidableEq` instance on `Turing.TM0.Stmt Γ`. -/
scoped instance instDecidableEqStmt {Γ : Type*} [DecidableEq Γ] : DecidableEq (TM0.Stmt Γ) :=
  Equiv.decidableEq stmtEquivSum

/-- Scoped `Primcodable` instance on `Turing.TM0.Stmt Γ` via `TM0.Stmt Γ ≃ Dir ⊕ Γ`. -/
scoped instance instPrimcodableStmt {Γ : Type*} [Primcodable Γ] : Primcodable (TM0.Stmt Γ) :=
  Primcodable.ofEquiv (Dir ⊕ Γ) stmtEquivSum

/-- Equivalence between `ListBlank Γ` and the subtype of trailing-blank-free lists. -/
def listBlankEquivCanonical {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] :
    ListBlank Γ ≃ { l : List Γ // l.rdropWhile (· == default) = l } where
  toFun L := ⟨L.trim, L.rdropWhile_trim⟩
  invFun s := ListBlank.mk s.1
  left_inv := ListBlank.mk_trim
  right_inv s := Subtype.ext ((ListBlank.trim_mk s.1).trans s.2)

/-- Scoped `Primcodable` instance on `ListBlank Γ` requiring only `[Inhabited Γ] [Primcodable Γ]`
(using `Encodable.decidableEqOfEncodable` internally to avoid any `[DecidableEq Γ]` diamond). -/
scoped instance instPrimcodableListBlank {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primcodable (ListBlank Γ) :=
  letI : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  letI : Primcodable { l : List Γ // l.rdropWhile (· == default) = l } :=
    Primcodable.subtype listBlank_canonical_primrecPred
  Primcodable.ofEquiv { l : List Γ // l.rdropWhile (· == default) = l } listBlankEquivCanonical

/-- Explicit equivalence between `Tape Γ` and `Γ × ListBlank Γ × ListBlank Γ`. -/
def tapeEquivProd {Γ : Type*} [Inhabited Γ] :
    Tape Γ ≃ Γ × ListBlank Γ × ListBlank Γ where
  toFun T := (T.head, T.left, T.right)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv T := by cases T; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

/-- Scoped `Primcodable` instance on `Tape Γ`. -/
scoped instance instPrimcodableTape {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primcodable (Tape Γ) :=
  Primcodable.ofEquiv (Γ × ListBlank Γ × ListBlank Γ) tapeEquivProd

/-- `tapeEquivProd` unfolds a `Tape` into `(T.head, T.left, T.right)`. -/
-- tier: T0
@[simp]
theorem tapeEquivProd_apply {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :
    tapeEquivProd T = (T.head, T.left, T.right) := by
  simp [tapeEquivProd]

/-- Explicit equivalence between `TM0.Cfg Γ Λ` and `Λ × Tape Γ`. -/
def cfgEquivProd {Γ Λ : Type*} [Inhabited Γ] :
    TM0.Cfg Γ Λ ≃ Λ × Tape Γ where
  toFun c := (c.q, c.Tape)
  invFun p := ⟨p.1, p.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl

/-- Scoped `Primcodable` instance on `TM0.Cfg Γ Λ`. -/
scoped instance instPrimcodableCfg {Γ Λ : Type*} [Inhabited Γ] [Primcodable Γ] [Primcodable Λ] :
    Primcodable (TM0.Cfg Γ Λ) :=
  Primcodable.ofEquiv (Λ × Tape Γ) cfgEquivProd

/-- `cfgEquivProd` unfolds a configuration `c` into `(c.q, c.Tape)`. -/
-- tier: T0
@[simp]
theorem cfgEquivProd_apply {Γ Λ : Type*} [Inhabited Γ] (c : TM0.Cfg Γ Λ) :
    cfgEquivProd c = (c.q, c.Tape) := by
  simp [cfgEquivProd]

/-! ## Primitive Recursive Operations on `ListBlank`, `Tape`, and `TM0.Cfg` -/

/-- Internal bridge characterizing `Primrec` into `ListBlank Γ` via `Encodable`'s decidable
equality before transferring to an arbitrary `[DecidableEq Γ]` instance. -/
-- tier: T2
theorem primrec_listBlank_iff_of_encodable {α Γ : Type*} [Primcodable α] [Inhabited Γ]
    [Primcodable Γ] {f : α → ListBlank Γ} :
    Primrec f ↔
      Primrec fun a ↦ @ListBlank.trim Γ _ (Encodable.decidableEqOfEncodable Γ) (f a) := by
  let _ : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  let _ : Primcodable { l : List Γ // l.rdropWhile (· == default) = l } :=
    Primcodable.subtype listBlank_canonical_primrecPred
  exact (Primrec.of_equiv_iff listBlankEquivCanonical).symm.trans
    (Primrec.subtype_val_iff (hp := listBlank_canonical_primrecPred)).symm

/-- A map `f : α → ListBlank Γ` is primitive recursive if and only if `a ↦ (f a).trim` is
primitive recursive (for any `[DecidableEq Γ]` instance). -/
-- tier: T2
theorem primrec_listBlank_iff {α Γ : Type*} [Primcodable α] [Inhabited Γ] [DecidableEq Γ]
    [Primcodable Γ] {f : α → ListBlank Γ} :
    Primrec f ↔ Primrec fun a ↦ (f a).trim :=
  primrec_listBlank_iff_of_encodable.trans
    ⟨fun h ↦ h.of_eq fun a ↦ ListBlank.trim_congr _ _ (f a),
      fun h ↦ h.of_eq fun a ↦ ListBlank.trim_congr _ _ (f a)⟩

/-- Quotienting a list into `ListBlank Γ` (`ListBlank.mk`) is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.listBlank_mk {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (ListBlank.mk : List Γ → ListBlank Γ) := by
  let _ : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  exact primrec_listBlank_iff.mpr <|
    (Primrec.list_rdropWhile (Primrec.beq.comp .id (.const default))).of_eq fun l ↦
      (ListBlank.trim_mk l).symm

/-- Extracting the canonical trailing-blank-free representative `ListBlank.trim` is primitive
recursive for any `[DecidableEq Γ]`. -/
-- tier: T1
theorem _root_.Primrec.listBlank_trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [Primcodable Γ] :
    Primrec (ListBlank.trim : ListBlank Γ → List Γ) :=
  (primrec_listBlank_iff (f := id)).mp .id

/-- Reading the head symbol of a `ListBlank Γ` is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.listBlank_head {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (ListBlank.head : ListBlank Γ → Γ) := by
  let _ : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  exact (Primrec.list_headI.comp Primrec.listBlank_trim).of_eq fun L ↦ by
    rw [← ListBlank.head_mk, ListBlank.mk_trim]

/-- Taking the tail of a `ListBlank Γ` is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.listBlank_tail {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (ListBlank.tail : ListBlank Γ → ListBlank Γ) := by
  let _ : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  exact (Primrec.listBlank_mk.comp (Primrec.list_tail.comp Primrec.listBlank_trim)).of_eq fun L ↦ by
    rw [← ListBlank.tail_mk, ListBlank.mk_trim]

/-- Prepending a symbol onto a `ListBlank Γ` (`ListBlank.cons`) is binary primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.listBlank_cons {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (ListBlank.cons : Γ → ListBlank Γ → ListBlank Γ) := by
  let _ : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  refine (Primrec.listBlank_mk.comp
    (Primrec.list_cons.comp .fst (Primrec.listBlank_trim.comp .snd))).to₂.of_eq fun a L ↦ ?_
  rw [← ListBlank.cons_mk, ListBlank.mk_trim]

/-- Indexing the `n`-th symbol of a `ListBlank Γ` (`ListBlank.nth`) is binary primitive
recursive. -/
-- tier: T1
theorem _root_.Primrec.listBlank_nth {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (ListBlank.nth : ListBlank Γ → ℕ → Γ) := by
  let _ : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  refine (Primrec.list_getI.comp (Primrec.listBlank_trim.comp .fst) .snd).to₂.of_eq fun L n ↦ ?_
  rw [← ListBlank.nth_mk, ListBlank.mk_trim]

/-- Projecting the current head symbol `Tape.head` of a `Tape Γ` is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_head {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (Tape.head : Tape Γ → Γ) :=
  Primrec.fst.comp (Primrec.of_equiv (e := tapeEquivProd))

/-- Projecting the left half-tape `Tape.left` of a `Tape Γ` is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_left {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (Tape.left : Tape Γ → ListBlank Γ) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := tapeEquivProd)))

/-- Projecting the right half-tape `Tape.right` of a `Tape Γ` is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_right {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (Tape.right : Tape Γ → ListBlank Γ) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := tapeEquivProd)))

/-- Constructing a `Tape Γ` from primitive recursive head, left, and right components is primitive
recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_mk {α Γ : Type*} [Primcodable α] [Inhabited Γ] [Primcodable Γ]
    {f : α → Γ} {g h : α → ListBlank Γ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a ↦ (⟨f a, g a, h a⟩ : Tape Γ)) :=
  (Primrec.of_equiv_symm (e := tapeEquivProd)).comp (hf.pair (hg.pair hh))

/-- Moving a `Tape Γ` in direction `Dir` (`Tape.move`) is binary primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_move {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.move : Dir → Tape Γ → Tape Γ) := by
  have hd : Primrec (fun p : Dir × Tape Γ ↦ dirEquivBool p.1) :=
    (Primrec.of_equiv (e := dirEquivBool)).comp .fst
  have hL : Primrec (fun p : Dir × Tape Γ ↦
      (⟨p.2.left.head, p.2.left.tail, p.2.right.cons p.2.head⟩ : Tape Γ)) :=
    Primrec.tape_mk
      (Primrec.listBlank_head.comp (Primrec.tape_left.comp .snd))
      (Primrec.listBlank_tail.comp (Primrec.tape_left.comp .snd))
      (Primrec.listBlank_cons.comp (Primrec.tape_head.comp .snd) (Primrec.tape_right.comp .snd))
  have hR : Primrec (fun p : Dir × Tape Γ ↦
      (⟨p.2.right.head, p.2.left.cons p.2.head, p.2.right.tail⟩ : Tape Γ)) :=
    Primrec.tape_mk
      (Primrec.listBlank_head.comp (Primrec.tape_right.comp .snd))
      (Primrec.listBlank_cons.comp (Primrec.tape_head.comp .snd) (Primrec.tape_left.comp .snd))
      (Primrec.listBlank_tail.comp (Primrec.tape_right.comp .snd))
  exact (Primrec.cond hd hR hL).to₂.of_eq fun d T ↦ by
    cases d <;> cases T <;> rfl

/-- Writing a symbol at the head of a `Tape Γ` (`Tape.write`) is binary primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_write {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.write : Γ → Tape Γ → Tape Γ) :=
  (Primrec.tape_mk .fst (Primrec.tape_left.comp .snd) (Primrec.tape_right.comp .snd)).to₂.of_eq
    fun _ ⟨_, _, _⟩ ↦ rfl

/-- Initializing a one-sided `Tape Γ` from a list (`Tape.mk₁`) is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_mk₁ {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (Tape.mk₁ : List Γ → Tape Γ) :=
  Primrec.tape_mk
    (Primrec.listBlank_head.comp Primrec.listBlank_mk)
    (.const (ListBlank.mk []))
    (Primrec.listBlank_tail.comp Primrec.listBlank_mk)

/-- Initializing a two-sided `Tape Γ` from left and inclusive-right lists (`Tape.mk₂`) is binary
primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_mk₂ {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.mk₂ : List Γ → List Γ → Tape Γ) :=
  (Primrec.tape_mk
    (Primrec.listBlank_head.comp (Primrec.listBlank_mk.comp .snd))
    (Primrec.listBlank_mk.comp .fst)
    (Primrec.listBlank_tail.comp (Primrec.listBlank_mk.comp .snd))).to₂

/-- Reading the symbol at signed integer offset `i : ℤ` on a `Tape Γ` (`Tape.nth`) is binary
primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_nth {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.nth : Tape Γ → ℤ → Γ) := by
  have hk : Primrec (fun p : Tape Γ × ℤ ↦ Encodable.encode p.2) := Primrec.encode.comp .snd
  have hd : Primrec (fun p : Tape Γ × ℤ ↦ (Encodable.encode p.2).div2) := Primrec.nat_div2.comp hk
  have hb : Primrec (fun p : Tape Γ × ℤ ↦ (Encodable.encode p.2).bodd) := Primrec.nat_bodd.comp hk
  have hneg : Primrec (fun p : Tape Γ × ℤ ↦ p.1.left.nth (Encodable.encode p.2).div2) :=
    Primrec.listBlank_nth.comp (Primrec.tape_left.comp .fst) hd
  have hpos : Primrec (fun p : Tape Γ × ℤ ↦
      ((Encodable.encode p.2).div2.casesOn p.1.head p.1.right.nth : Γ)) :=
    Primrec.nat_casesOn hd (Primrec.tape_head.comp .fst)
      (Primrec.listBlank_nth.comp (Primrec.tape_right.comp (Primrec.fst.comp .fst)) .snd).to₂
  refine (Primrec.cond hb hneg hpos).to₂.of_eq fun T i ↦ ?_
  rcases i with (_ | n) | n
  · dsimp only
    rw [show Encodable.encode (Int.ofNat 0) = 0 from rfl]
    rfl
  · have hb0 : (2 * (n + 1)).bodd = false := by simp
    have hd0 : (2 * (n + 1)).div2 = n + 1 := by rw [Nat.div2_val]; omega
    dsimp only
    rw [show Encodable.encode (Int.ofNat (n + 1)) = 2 * (n + 1) from rfl, hb0, hd0]
    rfl
  · have hb1 : (2 * n + 1).bodd = true := by simp
    have hd1 : (2 * n + 1).div2 = n := by rw [Nat.div2_val]; omega
    dsimp only
    rw [show Encodable.encode (Int.negSucc n) = 2 * n + 1 from rfl, hb1, hd1]
    rfl

/-- Extracting the inclusive right half-tape `Tape.right₀` is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.tape_right₀ {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (Tape.right₀ : Tape Γ → ListBlank Γ) :=
  Primrec.listBlank_cons.comp Primrec.tape_head Primrec.tape_right

/-- Projecting the machine state `TM0.Cfg.q` of a configuration is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.cfg_q {Γ Λ : Type*} [Inhabited Γ] [Primcodable Γ] [Primcodable Λ] :
    Primrec (TM0.Cfg.q : TM0.Cfg Γ Λ → Λ) :=
  Primrec.fst.comp (Primrec.of_equiv (e := cfgEquivProd))

/-- Projecting the tape `TM0.Cfg.Tape` of a configuration is primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.cfg_tape {Γ Λ : Type*} [Inhabited Γ] [Primcodable Γ] [Primcodable Λ] :
    Primrec (TM0.Cfg.Tape : TM0.Cfg Γ Λ → Tape Γ) :=
  Primrec.snd.comp (Primrec.of_equiv (e := cfgEquivProd))

/-- Constructing a configuration `TM0.Cfg Γ Λ` from primitive recursive state and tape maps is
primitive recursive. -/
-- tier: T1
theorem _root_.Primrec.cfg_mk {α Γ Λ : Type*} [Primcodable α] [Inhabited Γ] [Primcodable Γ]
    [Primcodable Λ] {f : α → Λ} {g : α → Tape Γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a ↦ (⟨f a, g a⟩ : TM0.Cfg Γ Λ)) :=
  (Primrec.of_equiv_symm (e := cfgEquivProd)).comp (hf.pair hg)

/-! ## `Encodable` Round-Trip Theorems -/

/-- Decoding an encoded `Turing.Dir` recovers the original direction. -/
-- tier: T0
theorem decode_encode_dir (d : Dir) :
    Encodable.decode (Encodable.encode d) = some d :=
  Encodable.encodek d

/-- Decoding an encoded `Turing.TM0.Stmt Γ` recovers the original statement. -/
-- tier: T0
theorem decode_encode_stmt {Γ : Type*} [Primcodable Γ] (s : TM0.Stmt Γ) :
    Encodable.decode (Encodable.encode s) = some s :=
  Encodable.encodek s

/-- Decoding an encoded `Turing.ListBlank Γ` recovers the original quotient half-tape. -/
-- tier: T0
theorem decode_encode_listBlank {Γ : Type*} [Inhabited Γ] [Primcodable Γ] (L : ListBlank Γ) :
    Encodable.decode (Encodable.encode L) = some L :=
  Encodable.encodek L

/-- Decoding an encoded `Turing.Tape Γ` recovers the original tape. -/
-- tier: T0
theorem decode_encode_tape {Γ : Type*} [Inhabited Γ] [Primcodable Γ] (T : Tape Γ) :
    Encodable.decode (Encodable.encode T) = some T :=
  Encodable.encodek T

/-- Decoding an encoded `Turing.TM0.Cfg Γ Λ` recovers the original configuration. -/
-- tier: T0
theorem decode_encode_cfg {Γ Λ : Type*} [Inhabited Γ] [Primcodable Γ] [Primcodable Λ]
    (c : TM0.Cfg Γ Λ) : Encodable.decode (Encodable.encode c) = some c :=
  Encodable.encodek c

end TuringRecursive

end
