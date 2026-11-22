/-
Copyright (c) 2026 TuringRecursive contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TuringRecursive contributors
-/
module

public import Mathlib.Computability.Halting
public import TuringRecursive.Equivalence

/-!
# Halting Undecidability, Uniform Compiler, and Exact-Output Windowed Universal `TM0`

This file implements Milestone M6 (`T-E(1)–(3)`):

* `TM0Code.halting_re` and `TM0Code.halting_not_computable` (`T-E(1)`): the uniform `TM0` halting
  predicate over `TM0Code × TM0.Cfg ℕ ℕ` is recursively enumerable (`REPred`) and undecidable
  (`¬ ComputablePred`).
* `TM0Code.exists_compiler`, `TM0Code.compile`, `TM0Code.primrec_compile`,
  `TM0Code.eval_compile_nat`, and `TM0Code.eval_compile` (`T-E(2)`): primitive recursive uniform
  compiler `TM0Code → Nat.Partrec.Code` via Kleene's $S^m_n$ theorem (`Nat.Partrec.Code.curry`).
* `encUniv`, `decUniv`, `primrec_encUniv`, `primrec_decUniv`, `decUniv_encNat_encode`,
  `UniversalΛ`, `U`, `U_eval`, `U_evalCfg_tape`, `U_mem_evalCfg_iff`, and `exists_universal_tm0`
  (`T-E(3)`): concrete fixed-alphabet universal `TM0` machine `U` over `Γ₀` whose full halting tape
  on `TM0.init (encUniv (m, c))` is literally `Tape.mk₁ (encNat (Encodable.encode c'))`.
-/

open Turing

namespace TuringRecursive

@[expose] public section

/-! ## `T-E(1)`: Uniform `TM0` Halting is `REPred` and Not `ComputablePred` -/

/-- The uniform `TM0` halting predicate over `TM0Code × TM0.Cfg ℕ ℕ` is recursively enumerable. -/
-- tier: T0
theorem TM0Code.halting_re :
    REPred fun p : TM0Code × TM0.Cfg ℕ ℕ ↦
      (StateTransition.eval (TM0.step p.1.machine) p.2).Dom :=
  Partrec.dom_re TM0Code.eval_partrec

/-- The uniform `TM0` halting predicate over `TM0Code × TM0.Cfg ℕ ℕ` is undecidable
(`¬ ComputablePred`). -/
-- tier: T2
theorem TM0Code.halting_not_computable :
    ¬ ComputablePred fun p : TM0Code × TM0.Cfg ℕ ℕ ↦
      (StateTransition.eval (TM0.step p.1.machine) p.2).Dom := by
  intro hComp
  let f : ℕ →. ℕ := fun n ↦ (Denumerable.ofNat Nat.Partrec.Code n).eval 0
  have hf : Nat.Partrec f :=
    Partrec.nat_iff.mp
      (Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0))
  obtain ⟨Λ, hFin, _, hInh, M, hM⟩ := nat_partrec_iff_exists_tm0.mp hf
  obtain ⟨fΓ, gΛ, m₀, _, _, hevalCfg, _⟩ := TM0Code.exists_relabeling M
  let r : Nat.Partrec.Code → TM0Code × TM0.Cfg ℕ ℕ := fun c ↦
    (m₀, TM0.init ((encNat (Encodable.encode c)).map fΓ))
  have hr : Primrec r :=
    (Primrec.const m₀).pair
      (TM0.init_primrec.comp
        (Primrec.list_map (primrec_encNat.comp Primrec.encode)
          ((Primrec.dom_finite (fΓ : Γ₀ → ℕ)).comp .snd).to₂))
  obtain ⟨hDec, hDecComp⟩ := hComp
  have hCodeComp : ComputablePred fun c : Nat.Partrec.Code ↦
      (StateTransition.eval (TM0.step (r c).1.machine) (r c).2).Dom :=
    ⟨fun c ↦ hDec (r c), hDecComp.comp hr.to_comp⟩
  refine ComputablePred.halting_problem 0 (hCodeComp.of_eq fun c ↦ ?_)
  have hinit :
      (TM0.init (encNat (Encodable.encode c)) : TM0.Cfg Γ₀ Λ).map fΓ gΛ =
        TM0.init ((encNat (Encodable.encode c)).map fΓ) :=
    TM0.map_init fΓ gΛ (encNat (Encodable.encode c))
  have hdom₁ :
      (StateTransition.eval (TM0.step m₀.machine) (r c).2).Dom ↔
        (StateTransition.eval (TM0.step M) (TM0.init (encNat (Encodable.encode c)))).Dom := by
    dsimp only [r]
    rw [← hinit, hevalCfg]
    simp
  have hdom₂ :
      (StateTransition.eval (TM0.step M) (TM0.init (encNat (Encodable.encode c)))).Dom ↔
        (TM0.eval M (encNat (Encodable.encode c))).Dom := by
    simp [TM0.eval]
  have hdom₃ :
      (TM0.eval M (encNat (Encodable.encode c))).Dom ↔ (c.eval 0).Dom := by
    rw [hM (Encodable.encode c)]
    simp [f]
  exact hdom₁.trans (hdom₂.trans hdom₃)

/-! ## `T-E(2)`: Uniform Primitive Recursive Compiler `TM0Code → Nat.Partrec.Code` -/

/-- Existence of a primitive recursive (hence computable) compiler `TM0Code → Nat.Partrec.Code`
translating every `TM0Code` into an equivalent `Nat.Partrec.Code` acting on all natural numbers
via `Encodable.decode (α := TM0.Cfg ℕ ℕ)` (and hence on encoded `TM0.Cfg ℕ ℕ` configurations). -/
-- tier: T2
theorem TM0Code.exists_compiler :
    ∃ compile : TM0Code → Nat.Partrec.Code,
      Primrec compile ∧
      (∀ (m : TM0Code) (n : ℕ),
        (compile m).eval n =
          (Part.ofOption (Encodable.decode (α := TM0.Cfg ℕ ℕ) n)).bind fun c ↦
            (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode) ∧
      ∀ (m : TM0Code) (c : TM0.Cfg ℕ ℕ),
        (compile m).eval (Encodable.encode c) =
          (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode := by
  let u : ℕ →. ℕ := fun x ↦
    (Part.ofOption (Encodable.decode (α := TM0Code) x.unpair.1)).bind fun m ↦
      (Part.ofOption (Encodable.decode (α := TM0.Cfg ℕ ℕ) x.unpair.2)).bind fun c ↦
        (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode
  have h1 : Partrec fun x : ℕ ↦ Part.ofOption (Encodable.decode (α := TM0Code) x.unpair.1) :=
    Computable.ofOption (Computable.decode.comp (Computable.fst.comp Computable.unpair))
  have h2 : Partrec fun p : ℕ × TM0Code ↦
      Part.ofOption (Encodable.decode (α := TM0.Cfg ℕ ℕ) p.1.unpair.2) :=
    Computable.ofOption
      (Computable.decode.comp (Computable.snd.comp (Computable.unpair.comp Computable.fst)))
  have h3 : Partrec fun q : (ℕ × TM0Code) × TM0.Cfg ℕ ℕ ↦
      (StateTransition.eval (TM0.step q.1.2.machine) q.2).map Encodable.encode :=
    (TM0Code.eval_partrec.comp (Computable.snd.comp Computable.fst) Computable.snd).map
      (Computable.encode.comp Computable.snd).to₂
  have hu : Nat.Partrec u := Partrec.nat_iff.mp (h1.bind (h2.bind h3.to₂).to₂)
  obtain ⟨cu, hcu⟩ := Nat.Partrec.Code.exists_code.mp hu
  refine ⟨fun m ↦ cu.curry (Encodable.encode m),
    Nat.Partrec.Code.primrec₂_curry.comp (.const cu) Primrec.encode, ?_, ?_⟩
  · intro m n
    rw [Nat.Partrec.Code.eval_curry, congrFun hcu (Nat.pair (Encodable.encode m) n)]
    simp [u]
  · intro m c
    rw [Nat.Partrec.Code.eval_curry,
      congrFun hcu (Nat.pair (Encodable.encode m) (Encodable.encode c))]
    simp [u]

/-- Named compiler `TM0Code → Nat.Partrec.Code` selected from `TM0Code.exists_compiler`. -/
-- tier: T2
noncomputable def TM0Code.compile : TM0Code → Nat.Partrec.Code :=
  TM0Code.exists_compiler.choose

/-- The uniform compiler `TM0Code.compile` is primitive recursive. -/
-- tier: T0
theorem TM0Code.primrec_compile : Primrec TM0Code.compile :=
  TM0Code.exists_compiler.choose_spec.1

/-- Evaluating `TM0Code.compile m` on any `n : ℕ` decodes `n` as `TM0.Cfg ℕ ℕ` and simulates
`m.machine`. -/
-- tier: T0
theorem TM0Code.eval_compile_nat (m : TM0Code) (n : ℕ) :
    (TM0Code.compile m).eval n =
      (Part.ofOption (Encodable.decode (α := TM0.Cfg ℕ ℕ) n)).bind fun c ↦
        (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode :=
  TM0Code.exists_compiler.choose_spec.2.1 m n

/-- Evaluating `TM0Code.compile m` on `Encodable.encode c` simulates `m.machine` starting from
`c`. -/
-- tier: T0
theorem TM0Code.eval_compile (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    (TM0Code.compile m).eval (Encodable.encode c) =
      (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode :=
  TM0Code.exists_compiler.choose_spec.2.2 m c

/-! ## `T-E(3)`: Fixed Universal Encodings and Exact-Output Windowed Universal `TM0` -/

/-- Concrete named input encoder `(TM0Code × TM0.Cfg ℕ ℕ) → List Γ₀` for the universal `TM0`
machine `U`. -/
-- tier: T1
def encUniv (mc : TM0Code × TM0.Cfg ℕ ℕ) : List Γ₀ :=
  encNat (Encodable.encode mc)

/-- Concrete named output decoder `ListBlank Γ₀ → TM0.Cfg ℕ ℕ` for the universal `TM0` machine
`U`. Performs zero step-simulation: it applies `decNat` followed by `Encodable.decode`. -/
-- tier: T1
def decUniv (L : ListBlank Γ₀) : TM0.Cfg ℕ ℕ :=
  (Encodable.decode (decNat L)).getD default

/-- Unfolding identity for `encUniv` on a pair `(m, c)`. -/
-- tier: T0
theorem encUniv_apply (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    encUniv (m, c) = encNat (Encodable.encode (m, c)) :=
  by
  rewrite [encUniv]
  rfl

/-- Unfolding identity for `decUniv` on a `ListBlank Γ₀`. -/
-- tier: T0
theorem decUniv_apply (L : ListBlank Γ₀) :
    decUniv L = (Encodable.decode (decNat L)).getD default :=
  by
  rw [decUniv]

/-- The universal input encoder `encUniv` is primitive recursive. -/
-- tier: T1
theorem primrec_encUniv : Primrec encUniv :=
  primrec_encNat.comp Primrec.encode

/-- The universal output decoder `decUniv` is primitive recursive. -/
-- tier: T1
theorem primrec_decUniv : Primrec decUniv :=
  Primrec.option_getD.comp (Primrec.decode.comp primrec_decNat) (.const default)

/-- `decUniv` is a left inverse to `ListBlank.mk ∘ encNat ∘ Encodable.encode` on configurations
`TM0.Cfg ℕ ℕ`. -/
-- tier: T0
theorem decUniv_encNat_encode (c : TM0.Cfg ℕ ℕ) :
    decUniv (ListBlank.mk (encNat (Encodable.encode c))) = c := by
  simp [decUniv, decNat_encNat]

/-- Natural-number universal evaluator decoding `n` as `(m, c) : TM0Code × TM0.Cfg ℕ ℕ` and
returning `Encodable.encode c'` when `m.machine` halts at `c'` from `c`. -/
-- tier: T2
def univEvalNat (n : ℕ) : Part ℕ :=
  (Part.ofOption (Encodable.decode (α := TM0Code × TM0.Cfg ℕ ℕ) n)).bind fun mc ↦
    (StateTransition.eval (TM0.step mc.1.machine) mc.2).map Encodable.encode

/-- On `Encodable.encode (m, c)`, `univEvalNat` evaluates to
`(StateTransition.eval (TM0.step m.machine) c).map Encodable.encode`. -/
-- tier: T0
theorem univEvalNat_encode (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    univEvalNat (Encodable.encode (m, c)) =
      (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode := by
  simp [univEvalNat]

/-- `univEvalNat` is `Nat.Partrec` as a direct reformulation of `TM0Code.eval_partrec`. -/
-- tier: T2
theorem univEvalNat_partrec : Nat.Partrec univEvalNat :=
  TM0Code.eval_partrec

/-- Existence of a `ToPartrec.Code` computing `univEvalNat` on singleton argument lists. -/
-- tier: T2
theorem exists_univToPartrecCode :
    ∃ c : ToPartrec.Code, ∀ n : ℕ, c.eval [n] = (univEvalNat n).map ([·]) := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code
    (Nat.Partrec'.part_iff₁.mpr (Partrec.nat_iff.mpr univEvalNat_partrec))
  exact ⟨c, fun n ↦ hc ⟨[n], rfl⟩⟩

/-- Concrete `ToPartrec.Code` underlying the universal `TM0` machine `U`. -/
-- tier: T2
noncomputable def univCode : ToPartrec.Code :=
  exists_univToPartrecCode.choose

/-- `univCode` evaluates `[n]` to `(univEvalNat n).map ([·])` for every `n : ℕ`. -/
-- tier: T0
theorem univCode_eval (n : ℕ) :
    univCode.eval [n] = (univEvalNat n).map ([·]) :=
  exists_univToPartrecCode.choose_spec n

/-- State type of the named universal `TM0` machine `U`. -/
-- tier: T2
noncomputable def UniversalΛ : Type :=
  codeTM0Λ univCode

/-- Finite-type instance on the universal state space `UniversalΛ`. -/
-- tier: T2
noncomputable instance instFintypeUniversalΛ : Fintype UniversalΛ :=
  instFintypeCodeTM0Λ univCode

/-- Decidable-equality instance on the universal state space `UniversalΛ`. -/
-- tier: T2
noncomputable instance instDecidableEqUniversalΛ : DecidableEq UniversalΛ :=
  instDecidableEqCodeTM0Λ univCode

/-- Inhabited instance on the universal state space `UniversalΛ` (initial state of `U`). -/
-- tier: T2
noncomputable instance instInhabitedUniversalΛ : Inhabited UniversalΛ :=
  instInhabitedCodeTM0Λ univCode

/-- Named universal `TM0` machine `U` over `Γ₀`. -/
-- tier: T2
noncomputable def U : TM0.Machine Γ₀ UniversalΛ :=
  codeTM0 univCode

/-- Named exact halting-tape output theorem for `U`: `U` halts on `TM0.init (encUniv (m, c))` if
and only if `m.machine` halts on `c`, and its halting tape is literally
`Tape.mk₁ (encNat (Encodable.encode c'))`. -/
-- tier: T2
theorem U_evalCfg_tape (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    (StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c)))).map TM0.Cfg.Tape =
      (StateTransition.eval (TM0.step m.machine) c).map
        fun c' ↦ Tape.mk₁ (encNat (Encodable.encode c')) := by
  have h := codeTM0_evalCfg_tape univCode (univCode_eval (Encodable.encode (m, c)))
  change (StateTransition.eval (TM0.step (codeTM0 univCode))
    (TM0.init (encNat (Encodable.encode (m, c))))).map TM0.Cfg.Tape = _
  rw [h, univEvalNat_encode m c, Part.map_map]
  rfl

/-- Named universal evaluation equation for `U` with fixed `encUniv` and `decUniv`. -/
-- tier: T2
theorem U_eval (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    (TM0.eval U (encUniv (m, c))).map decUniv =
      StateTransition.eval (TM0.step m.machine) c := by
  have h := congrArg (Part.map (decUniv ∘ Tape.right₀)) (U_evalCfg_tape m c)
  have hL :
      ((StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c)))).map TM0.Cfg.Tape).map
          (decUniv ∘ Tape.right₀) =
        (TM0.eval U (encUniv (m, c))).map decUniv := by
    simp [TM0.eval, Part.map_map, Function.comp_def]
  have hR :
      ((StateTransition.eval (TM0.step m.machine) c).map
          fun c' ↦ Tape.mk₁ (encNat (Encodable.encode c'))).map (decUniv ∘ Tape.right₀) =
        StateTransition.eval (TM0.step m.machine) c := by
    rw [Part.map_map]
    refine Part.map_id' (fun c' ↦ ?_) _
    dsimp only [Function.comp_apply]
    rw [Tape.mk₁, Tape.mk₂, Tape.mk'_right₀]
    exact decUniv_encNat_encode c'
  exact hL.symm.trans (h.trans hR)

/-- Membership form of `U_evalCfg_tape` for direct window/cylinder consumption in CMPP B2. -/
-- tier: T2
theorem U_mem_evalCfg_iff (m : TM0Code) (c c' : TM0.Cfg ℕ ℕ) :
    c' ∈ StateTransition.eval (TM0.step m.machine) c ↔
      ∃ u' ∈ StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c))),
        u'.Tape = Tape.mk₁ (encNat (Encodable.encode c')) := by
  have h := U_evalCfg_tape m c
  generalize StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c))) = pU at h ⊢
  generalize StateTransition.eval (TM0.step m.machine) c = pm at h ⊢
  have hmem :
      Tape.mk₁ (encNat (Encodable.encode c')) ∈ pU.map TM0.Cfg.Tape ↔
        Tape.mk₁ (encNat (Encodable.encode c')) ∈
          pm.map fun d ↦ Tape.mk₁ (encNat (Encodable.encode d)) := by
    rw [h]
  constructor
  · intro hc'
    exact (Part.mem_map_iff _).mp (hmem.mpr ((Part.mem_map_iff _).mpr ⟨c', hc', rfl⟩))
  · intro hu
    obtain ⟨d, hd, hEq⟩ := (Part.mem_map_iff _).mp (hmem.mp ((Part.mem_map_iff _).mpr hu))
    have hR : ∀ x : TM0.Cfg ℕ ℕ,
        decUniv (Tape.mk₁ (encNat (Encodable.encode x))).right₀ = x := fun x ↦ by
      rw [Tape.mk₁, Tape.mk₂, Tape.mk'_right₀]
      exact decUniv_encNat_encode x
    have hd' : d = c' :=
      (hR d).symm.trans ((congrArg (fun T : Tape Γ₀ ↦ decUniv T.right₀) hEq).trans (hR c'))
    exact hd' ▸ hd

/-- **Universal and Exact-Output Windowed `TM0` Theorem**: there exists a single finite-state
`TM0` machine `U` over `Γ₀` that simulates every `(m, c) : TM0Code × TM0.Cfg ℕ ℕ` via the fixed
named maps `encUniv` and `decUniv`, and whose full halting tape on `TM0.init (encUniv (m, c))` is
**exactly** `Tape.mk₁ (encNat (Encodable.encode c'))` (blank-free on `0 .. L - 1` and `default`
everywhere outside, uniquely isolating `c'` on the cylinder `[-L, L]` of radius
`L = (encNat (Encodable.encode c')).length`). -/
-- tier: T2
theorem exists_universal_tm0 :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (_ : Inhabited Λ)
      (U : TM0.Machine Γ₀ Λ),
      (∀ (m : TM0Code) (c : TM0.Cfg ℕ ℕ),
        (TM0.eval U (encUniv (m, c))).map decUniv =
          StateTransition.eval (TM0.step m.machine) c) ∧
      (∀ (m : TM0Code) (c : TM0.Cfg ℕ ℕ),
        (StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c)))).map TM0.Cfg.Tape =
          (StateTransition.eval (TM0.step m.machine) c).map
            fun c' ↦ Tape.mk₁ (encNat (Encodable.encode c'))) :=
  ⟨UniversalΛ, inferInstance, inferInstance, inferInstance, U, U_eval, U_evalCfg_tape⟩

end

end TuringRecursive
