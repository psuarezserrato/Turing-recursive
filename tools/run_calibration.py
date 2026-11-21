#!/usr/bin/env python3
"""
tools/run_calibration.py — W0 Stratified 40-Lemma Calibration Benchmark for gemma4:12B

Evaluates `tools/gemma_loop.py` on 40 already-proved lemmas from pinned Mathlib (`fc4f59e5`)
across `Computability/{Primrec/*,Partrec,PartrecCode,StateTransition,TuringMachine/*}`:
  - 15 T0 (algebra / combinatorics / boilerplate: Tape, ListBlank, BlankExtends, BlankRel, simp)
  - 15 T1 (structured: Primrec compositions, Option/List combinators, induction on List/Tape/Dir)
  - 10 T2 (core: iteration, finite-domain encoding, rfindOpt, Code bounds, StateTransition/TM0 simulation)

Target declarations and near-duplicates are excluded from BM25 premise/proof retrieval AND
forbidden from being invoked directly or via `@[simp]` in candidate proofs.
"""

import argparse
import json
import os
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

TOOLS_DIR = Path(__file__).resolve().parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import gemma_loop
import index as bm25_index
import ledger
import workflow_control

COMMON_PREAMBLE = """import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.StateTransition
import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Computability.TuringMachine.PostTuringMachine
import TuringRecursive.Tactic.PrimrecTac

open Denumerable Encodable Function Relation
open Turing TM0 StateTransition Primrec TuringRecursive.Tactic
"""

CALIBRATION_BENCHMARK: List[Dict[str, Any]] = [
    # =========================================================================
    # TIER T0 (15 lemmas): algebra / combinatorics / boilerplate / simp / ext
    # =========================================================================
    {
        "id": "T0_01",
        "tier": "T0",
        "mathlib_name": "Turing.BlankExtends.refl",
        "spec_name": "cal_BlankExtends_refl",
        "exclude": ["Turing.BlankExtends.refl", "BlankExtends.refl"],
        "unsSimp": [],
        "statement": "theorem cal_BlankExtends_refl {Γ : Type*} [Inhabited Γ] (l : List Γ) : BlankExtends l l",
        "gold_proof": "⟨0, by simp⟩",
    },
    {
        "id": "T0_02",
        "tier": "T0",
        "mathlib_name": "Turing.BlankExtends.trans",
        "spec_name": "cal_BlankExtends_trans",
        "exclude": ["Turing.BlankExtends.trans", "BlankExtends.trans"],
        "unsSimp": [],
        "statement": (
            "theorem cal_BlankExtends_trans {Γ : Type*} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :\n"
            "    BlankExtends l₁ l₂ → BlankExtends l₂ l₃ → BlankExtends l₁ l₃"
        ),
        "gold_proof": "by\n  rintro ⟨i, rfl⟩ ⟨j, rfl⟩\n  exact ⟨i + j, by simp⟩",
    },
    {
        "id": "T0_03",
        "tier": "T0",
        "mathlib_name": "Turing.BlankRel.refl",
        "spec_name": "cal_BlankRel_refl",
        "exclude": ["Turing.BlankRel.refl", "BlankRel.refl"],
        "unsSimp": [],
        "statement": "theorem cal_BlankRel_refl {Γ : Type*} [Inhabited Γ] (l : List Γ) : BlankRel l l",
        "gold_proof": "Or.inl (BlankExtends.refl _)",
    },
    {
        "id": "T0_04",
        "tier": "T0",
        "mathlib_name": "Turing.BlankRel.symm",
        "spec_name": "cal_BlankRel_symm",
        "exclude": ["Turing.BlankRel.symm", "BlankRel.symm"],
        "unsSimp": [],
        "statement": (
            "theorem cal_BlankRel_symm {Γ : Type*} [Inhabited Γ] {l₁ l₂ : List Γ} :\n"
            "    BlankRel l₁ l₂ → BlankRel l₂ l₁"
        ),
        "gold_proof": "Or.symm",
    },
    {
        "id": "T0_05",
        "tier": "T0",
        "mathlib_name": "Turing.ListBlank.exists_cons",
        "spec_name": "cal_ListBlank_exists_cons",
        "exclude": ["Turing.ListBlank.exists_cons", "ListBlank.exists_cons", "exists_cons"],
        "unsSimp": [],
        "statement": (
            "theorem cal_ListBlank_exists_cons {Γ : Type*} [Inhabited Γ] (l : ListBlank Γ) :\n"
            "    ∃ a l', l = ListBlank.cons a l'"
        ),
        "gold_proof": "⟨_, _, (ListBlank.cons_head_tail _).symm⟩",
    },
    {
        "id": "T0_06",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.move_left_right",
        "spec_name": "cal_Tape_move_left_right",
        "exclude": ["Turing.Tape.move_left_right", "Tape.move_left_right", "move_left_right"],
        "unsSimp": ["Turing.Tape.move_left_right"],
        "statement": (
            "theorem cal_Tape_move_left_right {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :\n"
            "    (T.move Dir.left).move Dir.right = T"
        ),
        "gold_proof": "by simp [Tape.move]",
    },
    {
        "id": "T0_07",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.move_right_left",
        "spec_name": "cal_Tape_move_right_left",
        "exclude": ["Turing.Tape.move_right_left", "Tape.move_right_left", "move_right_left"],
        "unsSimp": ["Turing.Tape.move_right_left"],
        "statement": (
            "theorem cal_Tape_move_right_left {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :\n"
            "    (T.move Dir.right).move Dir.left = T"
        ),
        "gold_proof": "by simp [Tape.move]",
    },
    {
        "id": "T0_08",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.mk'_right₀",
        "spec_name": "cal_Tape_mk'_right0",
        "exclude": ["Turing.Tape.mk'_right₀", "Tape.mk'_right₀", "mk'_right₀"],
        "unsSimp": ["Turing.Tape.mk'_right₀"],
        "statement": (
            "theorem cal_Tape_mk'_right0 {Γ : Type*} [Inhabited Γ] (L R : ListBlank Γ) :\n"
            "    (Tape.mk' L R).right₀ = R"
        ),
        "gold_proof": "ListBlank.cons_head_tail _",
    },
    {
        "id": "T0_09",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.mk'_left_right₀",
        "spec_name": "cal_Tape_mk'_left_right0",
        "exclude": ["Turing.Tape.mk'_left_right₀", "Tape.mk'_left_right₀", "mk'_left_right₀"],
        "unsSimp": ["Turing.Tape.mk'_left_right₀"],
        "statement": (
            "theorem cal_Tape_mk'_left_right0 {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :\n"
            "    Tape.mk' T.left T.right₀ = T"
        ),
        "gold_proof": "by simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]",
    },
    {
        "id": "T0_10",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.exists_mk'",
        "spec_name": "cal_Tape_exists_mk'",
        "exclude": ["Turing.Tape.exists_mk'", "Tape.exists_mk'", "exists_mk'"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Tape_exists_mk' {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :\n"
            "    ∃ L R, T = Tape.mk' L R"
        ),
        "gold_proof": "⟨_, _, (Tape.mk'_left_right₀ _).symm⟩",
    },
    {
        "id": "T0_11",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.write_self",
        "spec_name": "cal_Tape_write_self",
        "exclude": ["Turing.Tape.write_self", "Tape.write_self", "write_self"],
        "unsSimp": ["Turing.Tape.write_self"],
        "statement": (
            "theorem cal_Tape_write_self {Γ : Type*} [Inhabited Γ] :\n"
            "    ∀ T : Tape Γ, T.write T.1 = T"
        ),
        "gold_proof": "by rintro ⟨⟩; rfl",
    },
    {
        "id": "T0_12",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.write_mk'",
        "spec_name": "cal_Tape_write_mk'",
        "exclude": ["Turing.Tape.write_mk'", "Tape.write_mk'", "write_mk'"],
        "unsSimp": ["Turing.Tape.write_mk'"],
        "statement": (
            "theorem cal_Tape_write_mk' {Γ : Type*} [Inhabited Γ] (b : Γ) (L R : ListBlank Γ) :\n"
            "    (Tape.mk' L R).write b = Tape.mk' L (R.tail.cons b)"
        ),
        "gold_proof": "by simp [Tape.mk']",
    },
    {
        "id": "T0_13",
        "tier": "T0",
        "mathlib_name": "Turing.Tape.map_mk'",
        "spec_name": "cal_Tape_map_mk'",
        "exclude": ["Turing.Tape.map_mk'", "Tape.map_mk'", "map_mk'"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Tape_map_mk' {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']\n"
            "    (f : PointedMap Γ Γ') (L R : ListBlank Γ) :\n"
            "    (Tape.mk' L R).map f = Tape.mk' (L.map f) (R.map f)"
        ),
        "gold_proof": "by simp only [Tape.mk', Tape.map, ListBlank.head_map, ListBlank.tail_map]",
    },
    {
        "id": "T0_14",
        "tier": "T0",
        "mathlib_name": "Turing.TM0.univ_supports",
        "spec_name": "cal_TM0_univ_supports",
        "exclude": ["Turing.TM0.univ_supports", "TM0.univ_supports", "univ_supports"],
        "unsSimp": [],
        "statement": (
            "theorem cal_TM0_univ_supports {Γ Λ : Type*} [Inhabited Λ] (M : TM0.Machine Γ Λ) :\n"
            "    TM0.Supports M Set.univ"
        ),
        "gold_proof": "by constructor <;> intros <;> apply Set.mem_univ",
    },
    {
        "id": "T0_15",
        "tier": "T0",
        "mathlib_name": "Computable.const",
        "spec_name": "cal_Computable_const",
        "exclude": ["Computable.const"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Computable_const {α σ : Type*} [Primcodable α] [Primcodable σ] (s : σ) :\n"
            "    Computable fun _ : α => s"
        ),
        "gold_proof": "(Primrec.const _).to_comp",
    },

    # =========================================================================
    # TIER T1 (15 lemmas): structured Primrec compositions, Option/List/Dir
    # =========================================================================
    {
        "id": "T1_01",
        "tier": "T1",
        "mathlib_name": "Primrec₂.pair",
        "spec_name": "cal_Primrec2_pair",
        "exclude": ["Primrec₂.pair"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec2_pair {α β : Type*} [Primcodable α] [Primcodable β] :\n"
            "    Primrec₂ (@Prod.mk α β)"
        ),
        "gold_proof": "Primrec.pair .fst .snd",
    },
    {
        "id": "T1_02",
        "tier": "T1",
        "mathlib_name": "Primrec₂.comp",
        "spec_name": "cal_Primrec2_comp",
        "exclude": ["Primrec₂.comp", "Primrec₂.comp₂"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec2_comp {α β γ σ : Type*} [Primcodable α] [Primcodable β]\n"
            "    [Primcodable γ] [Primcodable σ] {f : β → γ → σ} {g : α → β} {h : α → γ}\n"
            "    (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) :\n"
            "    Primrec fun a => f (g a) (h a)"
        ),
        "gold_proof": "Primrec.comp hf (hg.pair hh)",
    },
    {
        "id": "T1_03",
        "tier": "T1",
        "mathlib_name": "Primrec.option_bind₁",
        "spec_name": "cal_Primrec_option_bind1",
        "exclude": ["Primrec.option_bind₁", "option_bind₁"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_option_bind1 {α σ : Type*} [Primcodable α] [Primcodable σ]\n"
            "    {f : α → Option σ} (hf : Primrec f) :\n"
            "    Primrec fun o => Option.bind o f"
        ),
        "gold_proof": "Primrec.option_bind .id (hf.comp Primrec.snd).to₂",
    },
    {
        "id": "T1_04",
        "tier": "T1",
        "mathlib_name": "Primrec.option_map₁",
        "spec_name": "cal_Primrec_option_map1",
        "exclude": ["Primrec.option_map₁", "option_map₁"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_option_map1 {α σ : Type*} [Primcodable α] [Primcodable σ]\n"
            "    {f : α → σ} (hf : Primrec f) :\n"
            "    Primrec (Option.map f)"
        ),
        "gold_proof": "Primrec.option_map .id (hf.comp Primrec.snd).to₂",
    },
    {
        "id": "T1_05",
        "tier": "T1",
        "mathlib_name": "Primrec.option_getD_default",
        "spec_name": "cal_Primrec_option_getD_default",
        "exclude": ["Primrec.option_getD_default", "option_getD_default"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_option_getD_default {α : Type*} [Primcodable α] [Inhabited α] :\n"
            "    Primrec (fun o : Option α => o.getD default)"
        ),
        "gold_proof": "Primrec.option_getD.comp .id (Primrec.const default)",
    },
    {
        "id": "T1_06",
        "tier": "T1",
        "mathlib_name": "Primrec.option_isSome",
        "spec_name": "cal_Primrec_option_isSome",
        "exclude": ["Primrec.option_isSome", "option_isSome"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_option_isSome {α : Type*} [Primcodable α] :\n"
            "    Primrec (@Option.isSome α)"
        ),
        "gold_proof": "(Primrec.option_casesOn .id (Primrec.const false) (Primrec.const true).to₂).of_eq fun o => by cases o <;> rfl",
    },
    {
        "id": "T1_07",
        "tier": "T1",
        "mathlib_name": "Primrec.nat_double",
        "spec_name": "cal_Primrec_nat_double",
        "exclude": ["Primrec.nat_double", "nat_double", "Primrec.nat_double_succ", "nat_double_succ"],
        "unsSimp": [],
        "statement": "theorem cal_Primrec_nat_double : Primrec (fun n : ℕ => 2 * n)",
        "gold_proof": "Primrec.nat_mul.comp (Primrec.const _) Primrec.id",
    },
    {
        "id": "T1_08",
        "tier": "T1",
        "mathlib_name": "Primrec.nat_double_succ",
        "spec_name": "cal_Primrec_nat_double_succ",
        "exclude": ["Primrec.nat_double_succ", "nat_double_succ"],
        "unsSimp": [],
        "statement": "theorem cal_Primrec_nat_double_succ : Primrec (fun n : ℕ => 2 * n + 1)",
        "gold_proof": "Primrec.succ.comp Primrec.nat_double",
    },
    {
        "id": "T1_09",
        "tier": "T1",
        "mathlib_name": "Primrec.list_head?",
        "spec_name": "cal_Primrec_list_head?",
        "exclude": ["Primrec.list_head?", "list_head?", "Computable.list_head?"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_list_head? {α : Type*} [Primcodable α] :\n"
            "    Primrec (@List.head? α)"
        ),
        "gold_proof": (
            "(Primrec.list_casesOn .id (Primrec.const none) "
            "(Primrec.option_some_iff.2 <| Primrec.fst.comp Primrec.snd).to₂).of_eq fun l => by cases l <;> rfl"
        ),
    },
    {
        "id": "T1_10",
        "tier": "T1",
        "mathlib_name": "Primrec.list_tail",
        "spec_name": "cal_Primrec_list_tail",
        "exclude": ["Primrec.list_tail", "list_tail", "Computable.list_tail"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_list_tail {α : Type*} [Primcodable α] :\n"
            "    Primrec (@List.tail α)"
        ),
        "gold_proof": (
            "(Primrec.list_casesOn .id (Primrec.const []) "
            "(Primrec.snd.comp Primrec.snd).to₂).of_eq fun l => by cases l <;> rfl"
        ),
    },
    {
        "id": "T1_11",
        "tier": "T1",
        "mathlib_name": "Primrec.list_concat",
        "spec_name": "cal_Primrec_list_concat",
        "exclude": ["Primrec.list_concat", "list_concat", "Computable.list_concat"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_list_concat {α : Type*} [Primcodable α] :\n"
            "    Primrec₂ fun l (a : α) => l ++ [a]"
        ),
        "gold_proof": "Primrec.list_append.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))",
    },
    {
        "id": "T1_12",
        "tier": "T1",
        "mathlib_name": "Primrec.list_flatMap",
        "spec_name": "cal_Primrec_list_flatMap",
        "exclude": ["Primrec.list_flatMap", "list_flatMap"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_list_flatMap {α β σ : Type*} [Primcodable α] [Primcodable β]\n"
            "    [Primcodable σ] {f : α → List β} {g : α → β → List σ}\n"
            "    (hf : Primrec f) (hg : Primrec₂ g) :\n"
            "    Primrec (fun a => (f a).flatMap (g a))"
        ),
        "gold_proof": "Primrec.list_flatten.comp (Primrec.list_map hf hg)",
    },
    {
        "id": "T1_13",
        "tier": "T1",
        "mathlib_name": "Primrec.list_length",
        "spec_name": "cal_Primrec_list_length",
        "exclude": ["Primrec.list_length", "list_length", "Computable.list_length"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_list_length {α : Type*} [Primcodable α] :\n"
            "    Primrec (@List.length α)"
        ),
        "gold_proof": (
            "(Primrec.list_foldr (@Primrec.id (List α) _) (Primrec.const 0) <| "
            "Primrec.to₂ (Primrec.succ.comp <| Primrec.snd.comp Primrec.snd).to₂).of_eq "
            "fun l => by dsimp; induction l <;> simp [*]"
        ),
    },
    {
        "id": "T1_14",
        "tier": "T1",
        "mathlib_name": "Turing.ListBlank.append_mk",
        "spec_name": "cal_ListBlank_append_mk",
        "exclude": ["Turing.ListBlank.append_mk", "ListBlank.append_mk", "append_mk"],
        "unsSimp": ["Turing.ListBlank.append_mk"],
        "statement": (
            "theorem cal_ListBlank_append_mk {Γ : Type*} [Inhabited Γ] (l₁ l₂ : List Γ) :\n"
            "    ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂)"
        ),
        "gold_proof": (
            "by\n  induction l₁ <;>\n"
            "    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]"
        ),
    },
    {
        "id": "T1_15",
        "tier": "T1",
        "mathlib_name": "Turing.Tape.map_move",
        "spec_name": "cal_Tape_map_move",
        "exclude": ["Turing.Tape.map_move", "Tape.map_move", "map_move"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Tape_map_move {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']\n"
            "    (f : PointedMap Γ Γ') (T : Tape Γ) (d : Dir) :\n"
            "    (T.move d).map f = (T.map f).move d"
        ),
        "gold_proof": (
            "by\n  cases T\n  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map, "
            "ListBlank.map_cons, ListBlank.tail_map]"
        ),
    },

    # =========================================================================
    # TIER T2 (10 lemmas): core iteration, rfindOpt, Code, StateTransition, TM0
    # =========================================================================
    {
        "id": "T2_01",
        "tier": "T2",
        "mathlib_name": "Primrec.nat_iterate",
        "spec_name": "cal_Primrec_nat_iterate",
        "exclude": ["Primrec.nat_iterate", "nat_iterate"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_nat_iterate {α β : Type*} [Primcodable α] [Primcodable β]\n"
            "    {f : α → ℕ} {g : α → β} {h : α → β → β}\n"
            "    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :\n"
            "    Primrec fun a => (h a)^[f a] (g a)"
        ),
        "gold_proof": (
            "(Primrec.nat_rec' hf hg (hh.comp₂ Primrec₂.left <| Primrec.snd.comp₂ Primrec₂.right)).of_eq "
            "fun a => by induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']"
        ),
    },
    {
        "id": "T2_02",
        "tier": "T2",
        "mathlib_name": "Primrec.dom_finite",
        "spec_name": "cal_Primrec_dom_finite",
        "exclude": ["Primrec.dom_finite", "dom_finite"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_dom_finite {α σ : Type*} [Primcodable α] [Primcodable σ]\n"
            "    [Finite α] (f : α → σ) : Primrec f"
        ),
        "gold_proof": (
            "let ⟨l, _, m⟩ := Finite.exists_univ_list α\n"
            "Primrec.option_some_iff.1 <| by\n"
            "  have := decidableEqOfEncodable α\n"
            "  refine ((Primrec.list_getElem?₁ (l.map f)).comp (Primrec.list_idxOf₁ l)).of_eq fun a => ?_\n"
            "  rw [List.getElem?_map, List.getElem?_idxOf (m a), Option.map_some]"
        ),
    },
    {
        "id": "T2_03",
        "tier": "T2",
        "mathlib_name": "Primrec.list_drop",
        "spec_name": "cal_Primrec_list_drop",
        "exclude": ["Primrec.list_drop", "list_drop"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Primrec_list_drop {α : Type*} [Primcodable α] :\n"
            "    Primrec₂ (List.drop : ℕ → List α → List α)"
        ),
        "gold_proof": (
            "(Primrec.nat_iterate Primrec.fst Primrec.snd "
            "(Primrec.list_tail.comp₂ Primrec₂.right)).to₂.of_eq fun n l => l.tail_iterate n"
        ),
    },
    {
        "id": "T2_04",
        "tier": "T2",
        "mathlib_name": "Partrec.rfindOpt",
        "spec_name": "cal_Partrec_rfindOpt",
        "exclude": ["Partrec.rfindOpt", "rfindOpt"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Partrec_rfindOpt {α σ : Type*} [Primcodable α] [Primcodable σ]\n"
            "    {f : α → ℕ → Option σ} (hf : Computable₂ f) :\n"
            "    Partrec fun a => Nat.rfindOpt (f a)"
        ),
        "gold_proof": (
            "(Partrec.rfind (Primrec.option_isSome.to_comp.comp hf).partrec.to₂).bind "
            "(Computable.ofOption hf)"
        ),
    },
    {
        "id": "T2_05",
        "tier": "T2",
        "mathlib_name": "Nat.rfindOpt_mono",
        "spec_name": "cal_Nat_rfindOpt_mono",
        "exclude": ["Nat.rfindOpt_mono", "rfindOpt_mono"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Nat_rfindOpt_mono {α : Type*} {f : ℕ → Option α}\n"
            "    (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n) {a : α} :\n"
            "    a ∈ Nat.rfindOpt f ↔ ∃ n, a ∈ f n"
        ),
        "gold_proof": (
            "⟨Nat.rfindOpt_spec, fun ⟨n, h⟩ => by\n"
            "  have h' := Nat.rfindOpt_dom.2 ⟨_, _, h⟩\n"
            "  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec ⟨h', rfl⟩\n"
            "  have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)\n"
            "  simp at this; simp [this, Part.get_mem]⟩"
        ),
    },
    {
        "id": "T2_06",
        "tier": "T2",
        "mathlib_name": "Nat.Partrec.Code.encode_lt_comp",
        "spec_name": "cal_Code_encode_lt_comp",
        "exclude": ["Nat.Partrec.Code.encode_lt_comp", "encode_lt_comp"],
        "unsSimp": [],
        "statement": (
            "theorem cal_Code_encode_lt_comp (cf cg : Nat.Partrec.Code) :\n"
            "    encode cf < encode (Nat.Partrec.Code.comp cf cg) ∧\n"
            "      encode cg < encode (Nat.Partrec.Code.comp cf cg)"
        ),
        "gold_proof": (
            "by\n  have : encode (Nat.Partrec.Code.pair cf cg) < encode (Nat.Partrec.Code.comp cf cg) := by\n"
            "    simp [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]\n"
            "  exact (Nat.Partrec.Code.encode_lt_pair cf cg).imp (fun h => lt_trans h this) "
            "fun h => lt_trans h this"
        ),
    },
    {
        "id": "T2_07",
        "tier": "T2",
        "mathlib_name": "StateTransition.reaches_eval",
        "spec_name": "cal_StateTransition_reaches_eval",
        "exclude": ["StateTransition.reaches_eval", "reaches_eval"],
        "unsSimp": [],
        "statement": (
            "theorem cal_StateTransition_reaches_eval {σ : Type*} {f : σ → Option σ} {a b : σ}\n"
            "    (ab : StateTransition.Reaches f a b) :\n"
            "    StateTransition.eval f a = StateTransition.eval f b"
        ),
        "gold_proof": (
            "by\n  refine Part.ext fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩\n"
            "  · have ⟨ac, c0⟩ := StateTransition.mem_eval.1 h\n"
            "    exact StateTransition.mem_eval.2 ⟨(or_iff_left_of_imp fun cb ↦ "
            "(StateTransition.eval_maximal h).1 cb ▸ ReflTransGen.refl).1 "
            "(StateTransition.reaches_total ab ac), c0⟩\n"
            "  · have ⟨bc, c0⟩ := StateTransition.mem_eval.1 h\n"
            "    exact StateTransition.mem_eval.2 ⟨ab.trans bc, c0⟩"
        ),
    },
    {
        "id": "T2_08",
        "tier": "T2",
        "mathlib_name": "StateTransition.tr_eval",
        "spec_name": "cal_StateTransition_tr_eval",
        "exclude": ["StateTransition.tr_eval", "tr_eval", "StateTransition.tr_eval'", "tr_eval'"],
        "unsSimp": [],
        "statement": (
            "theorem cal_StateTransition_tr_eval {σ₁ σ₂ : Type*} {f₁ : σ₁ → Option σ₁}\n"
            "    {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂ → Prop}\n"
            "    (H : StateTransition.Respects f₁ f₂ tr) {a₁ b₁ : σ₁} {a₂ : σ₂}\n"
            "    (aa : tr a₁ a₂) (ab : b₁ ∈ StateTransition.eval f₁ a₁) :\n"
            "    ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ StateTransition.eval f₂ a₂"
        ),
        "gold_proof": (
            "by\n  obtain ⟨ab, b0⟩ := StateTransition.mem_eval.1 ab\n"
            "  rcases StateTransition.tr_reaches H aa ab with ⟨b₂, bb, ab⟩\n"
            "  refine ⟨_, bb, StateTransition.mem_eval.2 ⟨ab, ?_⟩⟩\n"
            "  have := H bb; rwa [b0] at this"
        ),
    },
    {
        "id": "T2_09",
        "tier": "T2",
        "mathlib_name": "Turing.TM0.step_supports",
        "spec_name": "cal_TM0_step_supports",
        "exclude": ["Turing.TM0.step_supports", "TM0.step_supports", "step_supports"],
        "unsSimp": [],
        "statement": (
            "theorem cal_TM0_step_supports {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]\n"
            "    (M : TM0.Machine Γ Λ) {S : Set Λ} (ss : TM0.Supports M S) :\n"
            "    ∀ {c c' : TM0.Cfg Γ Λ}, c' ∈ TM0.step M c → c.q ∈ S → c'.q ∈ S"
        ),
        "gold_proof": (
            "by\n  intro ⟨q, T⟩ c' h₁ h₂\n"
            "  rcases Option.map_eq_some_iff.1 h₁ with ⟨⟨q', a⟩, h, rfl⟩\n"
            "  exact ss.2 h h₂"
        ),
    },
    {
        "id": "T2_10",
        "tier": "T2",
        "mathlib_name": "Turing.TM0.Machine.map_step",
        "spec_name": "cal_TM0_Machine_map_step",
        "exclude": ["Turing.TM0.Machine.map_step", "Machine.map_step", "map_step"],
        "unsSimp": [],
        "statement": (
            "theorem cal_TM0_Machine_map_step {Γ Γ' Λ Λ' : Type*} [Inhabited Γ] [Inhabited Γ']\n"
            "    [Inhabited Λ] [Inhabited Λ'] (M : TM0.Machine Γ Λ) (f₁ : PointedMap Γ Γ')\n"
            "    (f₂ : PointedMap Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ) {S : Set Λ}\n"
            "    (f₂₁ : Function.RightInverse f₁ f₂) (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :\n"
            "    ∀ c : TM0.Cfg Γ Λ,\n"
            "      c.q ∈ S →\n"
            "        (TM0.step M c).map (TM0.Cfg.map f₁ g₁) =\n"
            "          TM0.step (M.map f₁ f₂ g₁ g₂) (TM0.Cfg.map f₁ g₁ c)"
        ),
        "gold_proof": (
            "by\n  rintro ⟨q, T⟩ h\n"
            "  unfold TM0.step TM0.Machine.map TM0.Cfg.map\n"
            "  simp only [Turing.Tape.map_fst, g₂₁ q h, f₂₁ _]\n"
            "  rcases M q T.1 with (_ | ⟨q', d | a⟩); · rfl\n"
            "  · simp only [Option.map_some, Tape.map_move f₁]; rfl\n"
            "  · simp only [Option.map_some, Tape.map_write]; rfl"
        ),
    },
]


def render_item_spec(item: Dict[str, Any], use_gold: bool = False) -> str:
    """Render a standalone spec file for a single benchmark item."""
    lines = [COMMON_PREAMBLE.strip(), ""]
    for u in item.get("unsSimp", []):
        lines.append(f"attribute [-simp] {u}")
    lines.append(f"-- Original Mathlib lemma: {item['mathlib_name']}")
    lines.append(f"-- tier: {item['tier']}")
    body = item["gold_proof"] if use_gold else "by\n  sorry"
    lines.append(f"{item['statement']} :=\n  {body}\n")
    return "\n".join(lines)


def verify_all_gold_proofs(repo_root: Path) -> int:
    """Verify in a single Lean check that all 40 gold benchmark declarations compile cleanly."""
    lines = [COMMON_PREAMBLE.strip(), ""]
    for item in CALIBRATION_BENCHMARK:
        for u in item.get("unsSimp", []):
            lines.append(f"attribute [-simp] {u}")
        lines.append(f"-- {item['id']} ({item['tier']}): {item['mathlib_name']}")
        lines.append(f"{item['statement']} :=\n  {item['gold_proof']}\n")

    with tempfile.TemporaryDirectory() as td:
        gold_file = Path(td) / "GoldVerify.lean"
        gold_file.write_text("\n".join(lines), encoding="utf-8")
        accepted, rc, diag, lean_ms, _ = gemma_loop.run_lean_check(gold_file, repo_root, timeout_sec=180.0)
        if not accepted:
            print(f"[FAIL] Gold verification failed (rc={rc}, {lean_ms:.0f}ms):\n{diag}", file=sys.stderr)
            return 1
        print(f"[OK] All {len(CALIBRATION_BENCHMARK)} gold proofs verified cleanly in {lean_ms:.0f} ms!")
        return 0


def run_benchmark(
    repo_root: Path,
    max_attempts: int = 5,
    filter_tier: Optional[str] = None,
    filter_id: Optional[str] = None,
    output_json: Optional[Path] = None,
) -> Dict[str, Any]:
    """Run the compiler-in-the-loop calibration benchmark on the 40 stratified Mathlib lemmas."""
    idx = bm25_index.RepositoryIndex.load_or_build(repo_root=repo_root)
    specs_dir = repo_root / ".agents" / "gemma_scratch" / "calibration_specs"
    specs_dir.mkdir(parents=True, exist_ok=True)

    items = [
        it for it in CALIBRATION_BENCHMARK
        if (not filter_tier or it["tier"] == filter_tier)
        and (not filter_id or it["id"] == filter_id)
    ]

    results: List[Dict[str, Any]] = []
    t_start = time.time()

    for idx_num, item in enumerate(items, 1):
        if workflow_control.WorkflowController(repo_root).is_paused():
            print("[PAUSED] Stopping calibration benchmark.", file=sys.stderr)
            break

        spec_path = specs_dir / f"{item['id']}_{item['spec_name']}.lean"
        spec_path.write_text(render_item_spec(item, use_gold=False), encoding="utf-8")

        item_t0 = time.time()
        res = gemma_loop.prove_spec_file(
            spec_path=spec_path,
            repo_root=repo_root,
            tier_override=item["tier"],
            max_attempts=max_attempts,
            milestone="W0",
            exclude=item["exclude"],
            idx=idx,
        )
        wall_s = time.time() - item_t0
        decl_res = res["results"][0] if res.get("results") else {}
        accepted = bool(decl_res.get("accepted"))
        acc_attempt = decl_res.get("accepted_at_attempt")
        attempts = decl_res.get("attempts", [])
        total_tok = sum(int(a.get("tokens", 0)) for a in attempts)

        rec = {
            "id": item["id"],
            "tier": item["tier"],
            "mathlib_name": item["mathlib_name"],
            "spec_name": item["spec_name"],
            "accepted": accepted,
            "accepted_at_attempt": acc_attempt,
            "attempts_used": len(attempts),
            "wall_seconds": round(wall_s, 2),
            "total_tokens": total_tok,
            "attempts": attempts,
        }
        results.append(rec)
        status_str = f"PASS@{acc_attempt}" if accepted else f"FAIL({len(attempts)})"
        print(
            f"[{idx_num:02d}/{len(items):02d}] {item['id']} ({item['tier']}) "
            f"{item['mathlib_name']:<35} -> {status_str:<8} ({wall_s:.1f}s, {total_tok} tok)",
            flush=True,
        )

        if output_json:
            output_json.parent.mkdir(parents=True, exist_ok=True)
            output_json.write_text(json.dumps({"results": results}, indent=2) + "\n", encoding="utf-8")

    total_wall = time.time() - t_start
    payload = {"total_wall_seconds": round(total_wall, 2), "results": results}
    if output_json:
        output_json.parent.mkdir(parents=True, exist_ok=True)
        output_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description="Run W0 40-lemma stratified gemma4:12B calibration benchmark")
    parser.add_argument("--root", default=None, help="Override repository root")
    parser.add_argument("--verify-gold", action="store_true", help="Verify all 40 gold Mathlib proofs compile")
    parser.add_argument("--max-attempts", type=int, default=5, help="Max attempts per lemma (default 5)")
    parser.add_argument("--tier", choices=["T0", "T1", "T2"], default=None, help="Filter by tier")
    parser.add_argument("--id", default=None, help="Filter by single benchmark item ID (e.g. T0_01)")
    parser.add_argument(
        "--output",
        default=".agents/gemma_scratch/calibration_results.json",
        help="Path to save incremental calibration JSON results",
    )
    args = parser.parse_args()

    root = bm25_index.resolve_repo_root(args.root)
    if args.verify_gold:
        return verify_all_gold_proofs(root)

    out_path = Path(args.output)
    if not out_path.is_absolute():
        out_path = root / out_path
    run_benchmark(
        repo_root=root,
        max_attempts=args.max_attempts,
        filter_tier=args.tier,
        filter_id=args.id,
        output_json=out_path,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
