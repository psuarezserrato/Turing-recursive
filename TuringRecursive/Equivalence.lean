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

public import Mathlib.Computability.TuringMachine.ToPartrec
public import TuringRecursive.Uniform

/-!
# Fixed Alphabet `Γ₀`, Concrete `encNat` / `decNat`, and Church–Turing Equivalence

This file implements Milestone M5 (`T-D`) and the reusable finite-support `TM0` compilation bridge
for Milestone M6 (`T-E`):

* `kPrimeEquivFin4`, `instFintypeK'`, `gammaPrimeEquivFin4`, `Γ₀`, `instDecidableEqΓ₀`,
  `gamma0Equiv`, `instPrimcodableΓ₀`, `decode_encode_Γ₀`: the fixed 1250-symbol `TM0` tape alphabet
  induced by Mathlib's `PartrecToTM2` → `TM2to1` → `TM1to0` pipeline and its scoped `Fintype`,
  `DecidableEq`, and `Primcodable` instances.
* `encNat`, `decNat`, `default_notMem_encNat`, `primrec_encNat`, `primrec_decNat`, `decNat_encNat`:
  concrete named natural-number tape encoding and Horner-scheme left-inverse decoder over `Γ₀`.
* `restrictSupportedTM0`, `codeTM0Λ`, `codeTM0`, `codeTM0_evalCfg_tape`, `codeTM0_eval`:
  restriction of finitely supported `TM0` machines to subtype state spaces preserving full halting
  tapes, instantiated on compiled `Turing.ToPartrec.Code` programs.
* `nat_partrec_iff_exists_tm0`: bidirectional Church–Turing equivalence between `Nat.Partrec` and
  finite-state `TM0` computability over `Γ₀` with respect to `encNat`.
-/

open Turing

namespace TuringRecursive

@[expose] public section

/-! ## Fixed Tape Alphabet `Γ₀` and Scoped Instances -/

/-- Explicit 4-element equivalence `PartrecToTM2.K' ≃ Fin 4` (Mathlib provides `DecidableEq` and
`Inhabited` on `PartrecToTM2.K'` with `default = .main`, but no `Fintype` instance). -/
def kPrimeEquivFin4 : PartrecToTM2.K' ≃ Fin 4 where
  toFun
    | .main => 0
    | .rev => 1
    | .aux => 2
    | .stack => 3
  invFun
    | ⟨0, _⟩ => .main
    | ⟨1, _⟩ => .rev
    | ⟨2, _⟩ => .aux
    | ⟨3, _⟩ => .stack
  left_inv k := by cases k <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> try rfl
    omega

/-- `kPrimeEquivFin4` maps `.main` to `0`. -/
-- tier: T0
@[simp]
theorem kPrimeEquivFin4_main : kPrimeEquivFin4 .main = 0 := by
  simp [kPrimeEquivFin4]

/-- `kPrimeEquivFin4` maps `.rev` to `1`. -/
-- tier: T0
@[simp]
theorem kPrimeEquivFin4_rev : kPrimeEquivFin4 .rev = 1 := by
  simp [kPrimeEquivFin4]

/-- `kPrimeEquivFin4` maps `.aux` to `2`. -/
-- tier: T0
@[simp]
theorem kPrimeEquivFin4_aux : kPrimeEquivFin4 .aux = 2 := by
  simp [kPrimeEquivFin4]

/-- `kPrimeEquivFin4` maps `.stack` to `3`. -/
-- tier: T0
@[simp]
theorem kPrimeEquivFin4_stack : kPrimeEquivFin4 .stack = 3 := by
  simp [kPrimeEquivFin4]

/-- Scoped `Fintype` instance on `PartrecToTM2.K'`. -/
scoped instance instFintypeK' : Fintype PartrecToTM2.K' :=
  Fintype.ofEquiv (Fin 4) kPrimeEquivFin4.symm

/-- Explicit 4-element equivalence `PartrecToTM2.Γ' ≃ Fin 4`. -/
def gammaPrimeEquivFin4 : PartrecToTM2.Γ' ≃ Fin 4 where
  toFun
    | .consₗ => 0
    | .cons => 1
    | .bit0 => 2
    | .bit1 => 3
  invFun
    | ⟨0, _⟩ => .consₗ
    | ⟨1, _⟩ => .cons
    | ⟨2, _⟩ => .bit0
    | ⟨3, _⟩ => .bit1
  left_inv a := by cases a <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> try rfl
    omega

/-- `gammaPrimeEquivFin4` maps `.consₗ` to `0`. -/
-- tier: T0
@[simp]
theorem gammaPrimeEquivFin4_consₗ : gammaPrimeEquivFin4 .consₗ = 0 := by
  simp [gammaPrimeEquivFin4]

/-- `gammaPrimeEquivFin4` maps `.cons` to `1`. -/
-- tier: T0
@[simp]
theorem gammaPrimeEquivFin4_cons : gammaPrimeEquivFin4 .cons = 1 := by
  simp [gammaPrimeEquivFin4]

/-- `gammaPrimeEquivFin4` maps `.bit0` to `2`. -/
-- tier: T0
@[simp]
theorem gammaPrimeEquivFin4_bit0 : gammaPrimeEquivFin4 .bit0 = 2 := by
  simp [gammaPrimeEquivFin4]

/-- `gammaPrimeEquivFin4` maps `.bit1` to `3`. -/
-- tier: T0
@[simp]
theorem gammaPrimeEquivFin4_bit1 : gammaPrimeEquivFin4 .bit1 = 3 := by
  simp [gammaPrimeEquivFin4]

/-- Fixed finite tape alphabet `Bool × (PartrecToTM2.K' → Option PartrecToTM2.Γ')` induced by
Mathlib's `PartrecToTM2` → `TM2to1` → `TM1to0` pipeline (cardinality `2 × 5⁴ = 1250`, blank symbol
`default = (false, fun _ ↦ none)`). -/
abbrev Γ₀ : Type :=
  TM2to1.Γ' PartrecToTM2.K' (fun _ ↦ PartrecToTM2.Γ')

/-- Scoped `DecidableEq` instance on `Γ₀`. -/
scoped instance instDecidableEqΓ₀ : DecidableEq Γ₀ :=
  inferInstanceAs (DecidableEq (Bool × (PartrecToTM2.K' → Option PartrecToTM2.Γ')))

/-- Explicit equivalence between `Γ₀` and `Bool × (Fin 4 → Option (Fin 4))`. -/
def gamma0Equiv : Γ₀ ≃ Bool × (Fin 4 → Option (Fin 4)) :=
  Equiv.prodCongr (Equiv.refl Bool)
    (Equiv.arrowCongr kPrimeEquivFin4 (Equiv.optionCongr gammaPrimeEquivFin4))

/-- Scoped `Primcodable` instance on `Γ₀`. -/
scoped instance instPrimcodableΓ₀ : Primcodable Γ₀ :=
  Primcodable.ofEquiv (Bool × (Fin 4 → Option (Fin 4))) gamma0Equiv

/-- Decoding an encoded `Γ₀` symbol recovers the original symbol. -/
-- tier: T0
theorem decode_encode_Γ₀ (a : Γ₀) :
    Encodable.decode (Encodable.encode a) = some a := by
  simp

/-! ## Concrete Natural-Number Tape Encoding `encNat` and Decoder `decNat` -/

/-- Concrete named encoding of `n : ℕ` on the `TM0` tape alphabet `Γ₀`, induced directly by
Mathlib's `TM2to1.trInit` and `PartrecToTM2.trList [n]`. -/
def encNat (n : ℕ) : List Γ₀ :=
  TM2to1.trInit (Γ := fun _ ↦ PartrecToTM2.Γ') PartrecToTM2.K'.main (PartrecToTM2.trList [n])

/-- Concrete named left-inverse decoder `ListBlank Γ₀ → ℕ` reading the big-endian binary digits on
stack `.main` after stripping trailing blanks and dropping the stack-bottom head marker. -/
def decNat (L : ListBlank Γ₀) : ℕ :=
  L.trim.tail.foldl (fun acc x ↦
    match x.2 PartrecToTM2.K'.main with
    | some .bit0 => 2 * acc
    | some .bit1 => 2 * acc + 1
    | _ => acc) 0

/-- Embed a single `PartrecToTM2.Γ'` symbol onto stack `.main` of `Γ₀` with stack-bottom flag `b`
and `none` on the other three stacks. -/
-- tier: T1
def mkMainΓ₀ (b : Bool) (a : PartrecToTM2.Γ') : Γ₀ :=
  (b, Function.update (fun _ ↦ none) PartrecToTM2.K'.main (some a))

/-- Explicit head-and-tail expansion of `encNat n`: the stack-bottom `.cons` marker followed by
the big-endian binary digits `(PartrecToTM2.trNat n).reverse` on stack `.main`. -/
-- tier: T1
theorem encNat_eq (n : ℕ) :
    encNat n =
      mkMainΓ₀ true .cons :: (PartrecToTM2.trNat n).reverse.map (mkMainΓ₀ false) := by
  unfold encNat TM2to1.trInit mkMainΓ₀
  rw [show PartrecToTM2.trList [n] = PartrecToTM2.trNat n ++ [.cons] from rfl, List.reverse_append]
  rfl

/-- Every symbol of `encNat n` carries `some _ ≠ none` on `.main`, so the blank symbol `default`
never occurs in `encNat n`. -/
-- tier: T1
theorem default_notMem_encNat (n : ℕ) : (default : Γ₀) ∉ encNat n := by
  rw [encNat_eq, List.mem_cons, List.mem_map]
  rintro (h | ⟨a, _, h⟩)
  · exact Bool.false_ne_true (congrArg Prod.fst h)
  · have h2 : (mkMainΓ₀ false a).2 .main = (default : Γ₀).2 .main :=
      congrFun (congrArg Prod.snd h) .main
    simp [mkMainΓ₀, show (default : Γ₀) = (false, fun _ ↦ none) from rfl] at h2

/-- Little-endian binary increment on `List PartrecToTM2.Γ'` matching `PosNum.succ` and
`Num.succ`. -/
-- tier: T1
def succΓ'List : List PartrecToTM2.Γ' → List PartrecToTM2.Γ'
  | [] => [.bit1]
  | .bit1 :: l => .bit0 :: succΓ'List l
  | _ :: l => .bit1 :: l

/-- `succΓ'List` commutes with `PartrecToTM2.trPosNum` and `PosNum.succ`. -/
-- tier: T1
theorem succΓ'List_trPosNum :
    ∀ p : PosNum, succΓ'List (PartrecToTM2.trPosNum p) = PartrecToTM2.trPosNum p.succ
  | .one => rfl
  | .bit1 p => congrArg (List.cons PartrecToTM2.Γ'.bit0) (succΓ'List_trPosNum p)
  | .bit0 _ => rfl

/-- `succΓ'List` commutes with `PartrecToTM2.trNum` and `Num.succ`. -/
-- tier: T1
theorem succΓ'List_trNum :
    ∀ x : Num, succΓ'List (PartrecToTM2.trNum x) = PartrecToTM2.trNum x.succ
  | .zero => rfl
  | .pos p => succΓ'List_trPosNum p

/-- `PartrecToTM2.trNat n` equals `n`-fold iteration of `succΓ'List` starting from `[]`. -/
-- tier: T1
theorem trNat_eq_iterate_succΓ'List :
    ∀ n : ℕ, PartrecToTM2.trNat n = succΓ'List^[n] []
  | 0 => rfl
  | n + 1 => by
    have hsucc : ((n + 1 : ℕ) : Num) = (n : Num).succ := by
      rw [Nat.cast_succ, Num.add_one]
    calc
      PartrecToTM2.trNat (n + 1) = PartrecToTM2.trNum ((n + 1 : ℕ) : Num) := rfl
      _ = PartrecToTM2.trNum (n : Num).succ := by rw [hsucc]
      _ = succΓ'List (PartrecToTM2.trNat n) := (succΓ'List_trNum (n : Num)).symm
      _ = succΓ'List (succΓ'List^[n] []) := by rw [trNat_eq_iterate_succΓ'List n]
      _ = succΓ'List^[n + 1] [] := (Function.iterate_succ_apply' succΓ'List n []).symm

/-- Little-endian binary increment on `List (Fin 4)` mirroring `succΓ'List` along
`gammaPrimeEquivFin4`. -/
-- tier: T1
def succFin4List (l : List (Fin 4)) : List (Fin 4) :=
  List.recOn l [3] fun b tl ih ↦
    if b = (3 : Fin 4) then (2 : Fin 4) :: ih else (3 : Fin 4) :: tl

/-- `gammaPrimeEquivFin4` intertwines `succΓ'List` with `succFin4List`. -/
-- tier: T1
theorem map_gammaPrimeEquivFin4_succΓ'List (l : List PartrecToTM2.Γ') :
    (succΓ'List l).map gammaPrimeEquivFin4 = succFin4List (l.map gammaPrimeEquivFin4) := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    cases a
    · rfl
    · rfl
    · rfl
    · change (2 : Fin 4) :: (succΓ'List tl).map gammaPrimeEquivFin4 =
        if (3 : Fin 4) = (3 : Fin 4) then (2 : Fin 4) :: succFin4List (tl.map gammaPrimeEquivFin4)
        else (3 : Fin 4) :: tl.map gammaPrimeEquivFin4
      simp [ih]

/-- `succFin4List` is primitive recursive. -/
-- tier: T1
theorem primrec_succFin4List : Primrec succFin4List := by
  have hb : Primrec fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦ x.2.1 :=
    Primrec.fst.comp .snd
  have htl : Primrec fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦ x.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp .snd)
  have hih : Primrec fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦ x.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp .snd)
  have hcond : PrimrecPred fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦
      x.2.1 = (3 : Fin 4) :=
    Primrec.eq.comp hb (.const (3 : Fin 4))
  have hstep : Primrec₂ fun (_ : List (Fin 4)) (p : Fin 4 × List (Fin 4) × List (Fin 4)) ↦
      if p.1 = (3 : Fin 4) then (2 : Fin 4) :: p.2.2 else (3 : Fin 4) :: p.2.1 :=
    (Primrec.ite hcond
      (Primrec.list_cons.comp (.const (2 : Fin 4)) hih)
      (Primrec.list_cons.comp (.const (3 : Fin 4)) htl)).to₂
  exact (Primrec.list_rec .id (.const [(3 : Fin 4)]) hstep).of_eq fun _ ↦ rfl

/-- Mapping `PartrecToTM2.trNat n` into `List (Fin 4)` via `gammaPrimeEquivFin4` is primitive
recursive. -/
-- tier: T1
theorem primrec_map_trNat :
    Primrec fun n : ℕ ↦ (PartrecToTM2.trNat n).map gammaPrimeEquivFin4 := by
  have hiter : Primrec fun n : ℕ ↦ succFin4List^[n] [] :=
    Primrec.nat_iterate .id (.const []) (primrec_succFin4List.comp .snd).to₂
  refine hiter.of_eq fun n ↦ ?_
  rw [trNat_eq_iterate_succΓ'List n]
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      map_gammaPrimeEquivFin4_succΓ'List, ← ih]

/-- The natural-number tape encoding `encNat : ℕ → List Γ₀` is primitive recursive. -/
-- tier: T1
theorem primrec_encNat : Primrec encNat := by
  let f : Fin 4 → Γ₀ := fun i ↦ mkMainΓ₀ false (gammaPrimeEquivFin4.symm i)
  have htail : Primrec fun n : ℕ ↦
      ((PartrecToTM2.trNat n).map gammaPrimeEquivFin4).reverse.map f :=
    Primrec.list_map (Primrec.list_reverse.comp primrec_map_trNat)
      ((Primrec.dom_finite f).comp .snd).to₂
  refine (Primrec.list_cons.comp (.const (mkMainΓ₀ true .cons)) htail).of_eq fun n ↦ ?_
  rw [encNat_eq, ← List.map_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ ↦ ?_
  simp [f]

/-- The natural-number tape decoder `decNat : ListBlank Γ₀ → ℕ` is primitive recursive. -/
-- tier: T1
theorem primrec_decNat : Primrec decNat := by
  let coeff : Γ₀ → ℕ × ℕ := fun x ↦
    match x.2 PartrecToTM2.K'.main with
    | some .bit0 => (2, 0)
    | some .bit1 => (2, 1)
    | _ => (1, 0)
  have hc : Primrec coeff := Primrec.dom_finite coeff
  have hstep : Primrec₂ fun (_ : ListBlank Γ₀) (p : ℕ × Γ₀) ↦
      (coeff p.2).1 * p.1 + (coeff p.2).2 :=
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp ((Primrec.fst.comp hc).comp (Primrec.snd.comp .snd))
        (Primrec.fst.comp .snd))
      ((Primrec.snd.comp hc).comp (Primrec.snd.comp .snd))).to₂
  refine (Primrec.list_foldl (Primrec.list_tail.comp Primrec.listBlank_trim) (.const 0)
    hstep).of_eq fun L ↦ ?_
  dsimp only [decNat]
  congr 1
  funext acc x
  rcases hx : x.2 PartrecToTM2.K'.main with _ | (_ | _ | _ | _) <;> simp [coeff, hx]

/-- Single Horner-scheme binary step used by `decNat` on `PartrecToTM2.Γ'` stack symbols. -/
-- tier: T1
def digitStep (acc : ℕ) : PartrecToTM2.Γ' → ℕ
  | .bit0 => 2 * acc
  | .bit1 => 2 * acc + 1
  | _ => acc

/-- Big-endian Horner folding of `(PartrecToTM2.trPosNum p).reverse` evaluates to `(p : ℕ)`. -/
-- tier: T1
theorem foldl_digitStep_trPosNum :
    ∀ p : PosNum, (PartrecToTM2.trPosNum p).reverse.foldl digitStep 0 = (p : ℕ)
  | .one => rfl
  | .bit0 p => by
    simp only [PartrecToTM2.trPosNum, List.reverse_cons, List.foldl_append, List.foldl,
      digitStep, foldl_digitStep_trPosNum p, PosNum.cast_bit0]
    omega
  | .bit1 p => by
    simp only [PartrecToTM2.trPosNum, List.reverse_cons, List.foldl_append, List.foldl,
      digitStep, foldl_digitStep_trPosNum p, PosNum.cast_bit1]
    omega

/-- Big-endian Horner folding of `(PartrecToTM2.trNum x).reverse` evaluates to `(x : ℕ)`. -/
-- tier: T1
theorem foldl_digitStep_trNum :
    ∀ x : Num, (PartrecToTM2.trNum x).reverse.foldl digitStep 0 = (x : ℕ)
  | .zero => rfl
  | .pos p => foldl_digitStep_trPosNum p

/-- Decoding `ListBlank.mk (encNat n)` via `decNat` recovers `n` exactly. -/
-- tier: T1
theorem decNat_encNat (n : ℕ) : decNat (ListBlank.mk (encNat n)) = n := by
  have htrim : (ListBlank.mk (encNat n)).trim = encNat n := by
    rw [ListBlank.trim_mk, List.rdropWhile_eq_self_iff]
    intro hne hbeq
    exact default_notMem_encNat n (beq_iff_eq.mp hbeq ▸ List.getLast_mem hne)
  unfold decNat
  rw [htrim, encNat_eq, List.tail_cons, List.foldl_map]
  refine Eq.trans ?_ ((foldl_digitStep_trNum (n : Num)).trans (Num.to_of_nat n))
  congr 1
  funext acc a
  cases a <;> simp [mkMainΓ₀, digitStep]

/-! ## Finite-Support `TM0` Restriction and `ToPartrec.Code` Compilation Bridge -/

/-- Restrict a finitely supported `TM0.Machine Γ Λ` (`TM0.Supports M ↑S`) to the subtype state
space `↥S`. -/
-- tier: T2
def restrictSupportedTM0 {Γ Λ : Type*} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hs : TM0.Supports M ↑S) [Inhabited ↥S] :
    TM0.Machine Γ ↥S :=
  fun q a ↦
    match h : M q.1 a with
    | none => none
    | some (q', stmt) => some (⟨q', hs.2 h q.2⟩, stmt)

/-- Forgetful configuration map embedding `TM0.Cfg Γ ↥S` into `TM0.Cfg Γ Λ`. -/
-- tier: T2
def liftRestrictedCfg {Γ Λ : Type*} [Inhabited Γ] {S : Finset Λ}
    (c : TM0.Cfg Γ ↥S) : TM0.Cfg Γ Λ :=
  ⟨c.q.1, c.Tape⟩

/-- Single-step execution of `restrictSupportedTM0 M S hs` intertwines in lockstep with `M` along
`liftRestrictedCfg`. -/
-- tier: T2
theorem step_restrictSupportedTM0 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hs : TM0.Supports M ↑S) [Inhabited ↥S]
    (c : TM0.Cfg Γ ↥S) :
    TM0.step M (liftRestrictedCfg c) =
      (TM0.step (restrictSupportedTM0 M S hs) c).map liftRestrictedCfg := by
  rcases c with ⟨⟨q, hq⟩, T⟩
  unfold TM0.step restrictSupportedTM0 liftRestrictedCfg
  dsimp only
  split
  · next h =>
    exact congrArg (Option.map _) h
  · next q' stmt h =>
    refine (congrArg (Option.map _) h).trans ?_
    cases stmt <;> rfl

/-- Run-to-completion evaluation of `restrictSupportedTM0 M S hs` commutes with `liftRestrictedCfg`
on every initial configuration `c : TM0.Cfg Γ ↥S`. -/
-- tier: T2
theorem evalCfg_restrictSupportedTM0 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hs : TM0.Supports M ↑S) [Inhabited ↥S]
    (c : TM0.Cfg Γ ↥S) :
    StateTransition.eval (TM0.step M) (liftRestrictedCfg c) =
      (StateTransition.eval (TM0.step (restrictSupportedTM0 M S hs)) c).map liftRestrictedCfg :=
  StateTransition.eval_map_of_step_eq liftRestrictedCfg (step_restrictSupportedTM0 M S hs) c

/-- Restricting `M` to `↥S` preserves the full halting tape `StateTransition.eval ... (TM0.init l)`
whenever `(default : ↥S).1 = default`. -/
-- tier: T2
theorem evalCfg_tape_restrictSupportedTM0 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hs : TM0.Supports M ↑S) [Inhabited ↥S]
    (hdef : (default : ↥S).1 = default) (l : List Γ) :
    (StateTransition.eval (TM0.step (restrictSupportedTM0 M S hs)) (TM0.init l)).map
        TM0.Cfg.Tape =
      (StateTransition.eval (TM0.step M) (TM0.init l)).map TM0.Cfg.Tape := by
  have hinit : liftRestrictedCfg (TM0.init l : TM0.Cfg Γ ↥S) = TM0.init l := by
    simp [liftRestrictedCfg, TM0.init, hdef]
  rw [← hinit, evalCfg_restrictSupportedTM0 M S hs, Part.map_map]
  rfl

/-- Restricting `M` to `↥S` preserves `TM0.eval` on all input lists `l` whenever
`(default : ↥S).1 = default`. -/
-- tier: T2
theorem eval_restrictSupportedTM0 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hs : TM0.Supports M ↑S) [Inhabited ↥S]
    (hdef : (default : ↥S).1 = default) (l : List Γ) :
    TM0.eval (restrictSupportedTM0 M S hs) l = TM0.eval M l := by
  have h := congrArg (Part.map Tape.right₀) (evalCfg_tape_restrictSupportedTM0 M S hs hdef l)
  simpa [TM0.eval, Part.map_map, Function.comp_def] using h

/-- Two `ListBlank` elements over a dependent product are equal whenever all pointed coordinate
projections `proj i` agree. -/
-- tier: T2
theorem listBlank_eq_of_map_proj_eq {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)]
    {L₁ L₂ : ListBlank (∀ i, Γ i)}
    (h : ∀ i, L₁.map (proj i) = L₂.map (proj i)) : L₁ = L₂ := by
  refine ListBlank.ext fun n ↦ funext fun i ↦ ?_
  rw [← proj_map_nth, h i, proj_map_nth]

/-- Unique characterization of `TM2to1.TrCfg` at the halting configuration
`PartrecToTM2.halt [m]`: the `TM1` configuration must be `⟨none, none, Tape.mk₁ (encNat m)⟩`. -/
-- tier: T2
theorem trCfg_halt_singleton_iff (m : ℕ)
    (b₁ : TM1.Cfg Γ₀
      (TM2to1.Λ' PartrecToTM2.K' (fun _ ↦ PartrecToTM2.Γ')
        PartrecToTM2.Λ' (Option PartrecToTM2.Γ'))
      (Option PartrecToTM2.Γ')) :
    TM2to1.TrCfg (PartrecToTM2.halt [m]) b₁ ↔ b₁ = ⟨none, none, Tape.mk₁ (encNat m)⟩ := by
  let _ : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal .zero' .halt⟩
  have hinit := TM2to1.trCfg_init (Γ := fun _ ↦ PartrecToTM2.Γ') (Λ := PartrecToTM2.Λ')
    (σ := Option PartrecToTM2.Γ') PartrecToTM2.K'.main (PartrecToTM2.trList [m])
  change TM2to1.TrCfg (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [m]))
    (TM1.init (encNat m)) at hinit
  generalize hc₁ :
    (TM1.init (encNat m) :
      TM1.Cfg Γ₀
        (TM2to1.Λ' PartrecToTM2.K' (fun _ ↦ PartrecToTM2.Γ')
          PartrecToTM2.Λ' (Option PartrecToTM2.Γ'))
        (Option PartrecToTM2.Γ')) = c₁ at hinit
  cases hinit with
  | mk L₀ hL₀ =>
    have hTape₀ : Tape.mk₁ (encNat m) = Tape.mk' ∅ (TM2to1.addBottom L₀) :=
      congrArg TM1.Cfg.Tape hc₁
    have hL₀' : ∀ k,
        L₀.map (proj k) =
          ListBlank.mk
            ((PartrecToTM2.K'.elim (PartrecToTM2.trList [m]) [] [] [] k).map some).reverse := by
      intro k
      cases k <;> exact hL₀ _
    constructor
    · intro hb
      change TM2to1.TrCfg ⟨none, none, PartrecToTM2.K'.elim (PartrecToTM2.trList [m]) [] [] []⟩ b₁
        at hb
      cases hb with
      | mk L hL =>
        have hLL₀ : L = L₀ := listBlank_eq_of_map_proj_eq fun k ↦ (hL k).trans (hL₀' k).symm
        rw [hLL₀, ← hTape₀]
        rfl
    · rintro rfl
      rw [hTape₀]
      exact TM2to1.TrCfg.mk L₀ hL₀'

/-- `Inhabited` structure on `PartrecToTM2.Λ'` pointing at the start state `trNormal c .halt` of
`c : ToPartrec.Code`. -/
-- tier: T2
@[instance_reducible]
def instInhabitedCodeΛ₂ (c : ToPartrec.Code) : Inhabited PartrecToTM2.Λ' :=
  ⟨PartrecToTM2.trNormal c .halt⟩

/-- Intermediate `TM1` emulator of `PartrecToTM2.tr` associated to `c : ToPartrec.Code`. -/
-- tier: T2
def codeTM1 (_c : ToPartrec.Code) :=
  TM2to1.tr PartrecToTM2.tr

/-- Unbounded-state `TM0` emulator of `codeTM1 c` over `Γ₀`. -/
-- tier: T2
def codeRawTM0 (c : ToPartrec.Code) :=
  let _ : Inhabited PartrecToTM2.Λ' := instInhabitedCodeΛ₂ c
  TM1to0.tr (codeTM1 c)

/-- Finite `Finset` of `TM0` states reachable from the start state of `c : ToPartrec.Code`. -/
-- tier: T2
noncomputable def codeStateFinset (c : ToPartrec.Code) :=
  let _ : Inhabited PartrecToTM2.Λ' := instInhabitedCodeΛ₂ c
  TM1to0.trStmts (codeTM1 c) (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt))

/-- `codeStateFinset c` supports `codeRawTM0 c`. -/
-- tier: T2
theorem supports_codeRawTM0 (c : ToPartrec.Code) :
    let _ : Inhabited PartrecToTM2.Λ' := instInhabitedCodeΛ₂ c
    TM0.Supports (codeRawTM0 c) ↑(codeStateFinset c) := by
  let _ : Inhabited PartrecToTM2.Λ' := instInhabitedCodeΛ₂ c
  exact TM1to0.tr_supports (codeTM1 c)
    (TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports c .halt))

/-- Finite state space `↥(codeStateFinset c)` of the compiled `TM0` machine for
`c : ToPartrec.Code`. -/
-- tier: T2
def codeTM0Λ (c : ToPartrec.Code) : Type :=
  ↥(codeStateFinset c)

/-- `Fintype` instance on `codeTM0Λ c`. -/
-- tier: T2
noncomputable instance instFintypeCodeTM0Λ (c : ToPartrec.Code) : Fintype (codeTM0Λ c) :=
  Finset.Subtype.fintype (codeStateFinset c)

/-- `DecidableEq` instance on `codeTM0Λ c`. -/
-- tier: T2
noncomputable instance instDecidableEqCodeTM0Λ (c : ToPartrec.Code) : DecidableEq (codeTM0Λ c) :=
  Classical.decEq (codeTM0Λ c)

/-- `Inhabited` instance on `codeTM0Λ c` pointing at the initial `TM0` state of `c`. -/
-- tier: T2
instance instInhabitedCodeTM0Λ (c : ToPartrec.Code) : Inhabited (codeTM0Λ c) :=
  let _ : Inhabited PartrecToTM2.Λ' := instInhabitedCodeΛ₂ c
  ⟨⟨default, (supports_codeRawTM0 c).1⟩⟩

/-- Finite-state `TM0` machine over `Γ₀` compiling `c : ToPartrec.Code` via
`PartrecToTM2` → `TM2to1` → `TM1to0` → `restrictSupportedTM0`. -/
-- tier: T2
noncomputable def codeTM0 (c : ToPartrec.Code) : TM0.Machine Γ₀ (codeTM0Λ c) :=
  let _ : Inhabited PartrecToTM2.Λ' := instInhabitedCodeΛ₂ c
  let _ : Inhabited ↥(codeStateFinset c) := instInhabitedCodeTM0Λ c
  restrictSupportedTM0 (codeRawTM0 c) (codeStateFinset c) (supports_codeRawTM0 c)

/-- Exact halting-tape theorem for `codeTM0 c`: whenever `c.eval [n] = (f n).map ([·])`, running
`codeTM0 c` from `TM0.init (encNat n)` halts with full two-sided tape `Tape.mk₁ (encNat m)` for
`m ∈ f n` (and diverges when `f n = Part.none`). -/
-- tier: T2
theorem codeTM0_evalCfg_tape {f : ℕ →. ℕ} (c : ToPartrec.Code) {n : ℕ}
    (hc : c.eval [n] = (f n).map ([·])) :
    (StateTransition.eval (TM0.step (codeTM0 c)) (TM0.init (encNat n))).map TM0.Cfg.Tape =
      (f n).map (Tape.mk₁ ∘ encNat) := by
  let _ : Inhabited PartrecToTM2.Λ' := instInhabitedCodeΛ₂ c
  let _ : Inhabited ↥(codeStateFinset c) := instInhabitedCodeTM0Λ c
  have h0 :
      (StateTransition.eval (TM0.step (codeTM0 c)) (TM0.init (encNat n))).map TM0.Cfg.Tape =
        (StateTransition.eval (TM0.step (codeRawTM0 c)) (TM0.init (encNat n))).map TM0.Cfg.Tape :=
    evalCfg_tape_restrictSupportedTM0 (codeRawTM0 c) (codeStateFinset c) (supports_codeRawTM0 c)
      rfl (encNat n)
  have h10 :
      (StateTransition.eval (TM0.step (codeRawTM0 c)) (TM0.init (encNat n))).map TM0.Cfg.Tape =
        (StateTransition.eval (TM1.step (codeTM1 c)) (TM1.init (encNat n))).map TM1.Cfg.Tape := by
    have htr := StateTransition.tr_eval' (TM1.step (codeTM1 c)) (TM0.step (codeRawTM0 c))
      (TM1to0.trCfg (codeTM1 c)) (TM1to0.tr_respects (codeTM1 c)) (TM1.init (encNat n))
    change (StateTransition.eval (TM0.step (codeRawTM0 c))
      (TM1to0.trCfg (codeTM1 c) (TM1.init (encNat n)))).map TM0.Cfg.Tape = _
    rw [htr, Part.map_eq_map, Part.map_map]
    rfl
  have hinit₂ :
      TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [n]) = PartrecToTM2.init c [n] := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> rfl
  have heval₂ :
      StateTransition.eval (TM2.step PartrecToTM2.tr)
          (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [n])) =
        (f n).map fun m ↦ PartrecToTM2.halt [m] := by
    rw [hinit₂, PartrecToTM2.tr_eval c [n], hc, Part.map_eq_map, Part.map_map]
    rfl
  have heval₁ :
      StateTransition.eval (TM1.step (codeTM1 c)) (TM1.init (encNat n)) =
        (f n).map fun m ↦ ⟨none, none, Tape.mk₁ (encNat m)⟩ := by
    have hresp := TM2to1.tr_respects PartrecToTM2.tr
    have hinit₂₁ := TM2to1.trCfg_init (Γ := fun _ ↦ PartrecToTM2.Γ') (Λ := PartrecToTM2.Λ')
      (σ := Option PartrecToTM2.Γ') PartrecToTM2.K'.main (PartrecToTM2.trList [n])
    refine Part.ext fun b₁ ↦ ⟨fun hb₁ ↦ ?_, fun hb₁ ↦ ?_⟩
    · obtain ⟨b₂, hTr, hb₂⟩ := StateTransition.tr_eval_rev hresp hinit₂₁ hb₁
      rw [heval₂] at hb₂
      obtain ⟨m, hm, rfl⟩ := (Part.mem_map_iff _).1 hb₂
      exact (Part.mem_map_iff _).2 ⟨m, hm, ((trCfg_halt_singleton_iff m b₁).mp hTr).symm⟩
    · obtain ⟨m, hm, rfl⟩ := (Part.mem_map_iff _).1 hb₁
      have hb₂ : PartrecToTM2.halt [m] ∈
          StateTransition.eval (TM2.step PartrecToTM2.tr)
            (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [n])) :=
        heval₂.symm ▸ (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
      obtain ⟨b₁', hTr', hb₁'⟩ := StateTransition.tr_eval hresp hinit₂₁ hb₂
      rwa [(trCfg_halt_singleton_iff m b₁').mp hTr'] at hb₁'
  rw [h0, h10, heval₁, Part.map_map]
  rfl

/-- Output half-tape evaluation corollary of `codeTM0_evalCfg_tape`: whenever
`c.eval [n] = (f n).map ([·])`, running `codeTM0 c` on `encNat n` evaluates to
`(f n).map (ListBlank.mk ∘ encNat)`. -/
-- tier: T2
theorem codeTM0_eval {f : ℕ →. ℕ} (c : ToPartrec.Code) {n : ℕ}
    (hc : c.eval [n] = (f n).map ([·])) :
    TM0.eval (codeTM0 c) (encNat n) = (f n).map (ListBlank.mk ∘ encNat) := by
  have h := congrArg (Part.map Tape.right₀) (codeTM0_evalCfg_tape c hc)
  simpa [TM0.eval, Part.map_map, Function.comp_def, Tape.mk₁, Tape.mk₂] using h

/-! ## Church–Turing Equivalence for `TM0` (`T-D`) -/

/-- **Church–Turing Equivalence for `TM0`**: a partial function `f : ℕ →. ℕ` is `Nat.Partrec` if
and only if it is computed with respect to the fixed named encoding `encNat` by a `TM0` machine
over the fixed alphabet `Γ₀` and some finite state space `Λ`. -/
-- tier: T2
theorem nat_partrec_iff_exists_tm0 {f : ℕ →. ℕ} :
    Nat.Partrec f ↔
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (_ : Inhabited Λ)
        (M : TM0.Machine Γ₀ Λ),
        ∀ n : ℕ, TM0.eval M (encNat n) = (f n).map (ListBlank.mk ∘ encNat) := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ :=
      ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr (Partrec.nat_iff.mpr hf))
    refine ⟨codeTM0Λ c, inferInstance, inferInstance, inferInstance, codeTM0 c, fun n ↦ ?_⟩
    exact codeTM0_eval c (hc ⟨[n], rfl⟩)
  · rintro ⟨Λ, hFin, _, hInh, M, hM⟩
    let _ : Primcodable Λ := Primcodable.ofEquiv (Fin (Fintype.card Λ)) (Fintype.equivFin Λ)
    have heval : Partrec fun n : ℕ ↦ (TM0.eval M (encNat n)).map decNat :=
      ((TM0.eval_partrec M).comp primrec_encNat.to_comp).map
        ((primrec_decNat.comp .snd).to₂.to_comp)
    refine Partrec.nat_iff.mp (heval.of_eq fun n ↦ ?_)
    rw [hM n, Part.map_map]
    exact Part.map_id' decNat_encNat (f n)

end

end TuringRecursive
