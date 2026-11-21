# Milestone S1 Human-Review Specification: `TM → Partrec` Frozen Statements

- **Branch / Worktree**: `work/spec` (`.worktrees/spec`, never merged into `main`)
- **Lean Specification File**: `spec/Spec.lean` (661 lines, ≤100 columns throughout; **FROZEN SHA-256**: `b9ee4acddccaaadf68471374b570fd783e95dded44ac429183edc76e43afeb3a`)
- **Toolchain & Pinned Mathlib**: Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
- **Verification Command**: `LEAN_NUM_THREADS=2 lake env lean spec/Spec.lean` → **exit code `0`**, **0 errors**, **56 `sorry` warnings** (100% in `Prop`-valued `theorem` declarations; **0 `sorry`s** in `def`, `abbrev`, `structure`, or `instance` declarations).
- **Gate S1 Status**: **FROZEN** (`Q1`–`Q5` reviewed by `@verifier-tm` and approved by the user).

---

## 0. Executive Summary & Critical Review of `MISSION_DIRECTIVE.md`

Before freezing statements for Gate G3, we audited every item in `MISSION_DIRECTIVE.md` (§1 and §2) against the pinned Mathlib source and against **Route-1 anti-vacuity principles** (no statement may hold trivially via an existentially quantified encoding, a non-injective relabeling collapse, or an over-strong hypothesis). Below are the concrete findings, deviations/strengthenings relative to the directive text, and critiques of the directive itself:

1. **CRITICAL ANTI-VACUITY FIX in `T-C` (`TM0Code.exists_relabeling`)**:
   - *Directive flaw*: `MISSION_DIRECTIVE.md` §1 (`T-C`) states the relabeling theorem as the existence of `f : PointedMap Γ ℕ`, `g : PointedMap Λ ℕ`, and `m : TM0Code` commuting with `StateTransition.eval` and `TM0.eval`, **without asserting `Function.Injective f` or `Function.Injective g`**.
   - *Concrete vacuity exploit*: Take *any* machine `M` over `Bool` that halts on every input (e.g., a 1-step NOT gate flipping `false ↔ true`). Setting `f := ⟨fun _ ↦ 0, rfl⟩`, `g := ⟨fun _ ↦ 0, rfl⟩`, and `m := ⟨[]⟩` (the empty machine that halts immediately in 0 steps!) makes **both** `StateTransition.eval (TM0.step m.machine) (c.map f g) = (StateTransition.eval (TM0.step M) c).map (Cfg.map f g)` and `TM0.eval m.machine (l.map f) = (TM0.eval M l).map (ListBlank.map f)` hold identically (`Part.some ⟨0, default⟩ = Part.some ⟨0, default⟩`) while erasing 100% of `M`'s state/tape information! Moreover, downstream CMPP B2 must invert `Cfg.map f g` to distinguish target configurations.
   - *Fix in `Spec.lean`*: Added `Function.Injective f ∧ Function.Injective g` to `TM0Code.exists_relabeling`. In the `Finite.exists_equiv_fin` proof, injectivity is a 2-line consequence of `Fin.val_injective.comp e.injective`.

2. **Missing Mathlib Instances Caught (`TM0.Stmt`, `Γ₀`, `PartrecToTM2.K'`)**:
   - `Turing.TM0.Stmt` (`PostTuringMachine.lean:116`) does **not** derive `DecidableEq` in Mathlib, so `structure TM0Code ... deriving DecidableEq` fails unless `DecidableEq (TM0.Stmt Γ)` is provided. `Spec.lean` adds `scoped instance instDecidableEqStmt` via `stmtEquivSum : TM0.Stmt Γ ≃ Dir ⊕ Γ`.
   - `Turing.PartrecToTM2.K'` (`ToPartrec.lean:173–178`) **already** derives `DecidableEq` and `Inhabited` (`default = .main`) in Mathlib; only `Fintype PartrecToTM2.K'` is missing (`scoped instance instFintypeK'` via `kPrimeEquivFin4 : PartrecToTM2.K' ≃ Fin 4`).
   - `Γ₀ := TM2to1.Γ' PartrecToTM2.K' (fun _ ↦ PartrecToTM2.Γ')` inherits `Inhabited` (`StackTuringMachine.lean:352`) and `Fintype` (`StackTuringMachine.lean:355`, once `Fintype K'` is in scope), but Mathlib provides **neither** `DecidableEq` nor `Primcodable` on `TM2to1.Γ'`. `Spec.lean` adds computable `scoped instance instDecidableEqΓ₀` and `scoped instance instPrimcodableΓ₀` (via `Γ₀ ≃ Bool × (Fin 4 → Option (Fin 4))` and `Primcodable.finArrow`, 0 `sorry`s), which are required to state `Primrec encNat`, `Primrec decNat`, `Primrec encUniv`, and `Primrec decUniv`, and to apply `T-A` in `T-D(⇐)`.

3. **T-A′ Coercion Check (`TM0.exists_code_eval`)**:
   - The literal Kleene statement `∃ c : Nat.Partrec.Code, ∀ l, c.eval (Encodable.encode l) = (TM0.eval M l).map Encodable.encode` elaborates in Lean `v4.36.0` **verbatim without any coercions or type annotations** on `l` once `instPrimcodableListBlank` is in scope.

4. **Strengthening `T-E(3)` Windowed Output (`U_evalCfg_tape` + Cell-`L` Terminator Note)**:
   - *Directive subtlety 1 (divergence faithfulness)*: If the windowed theorem were stated only as `c' ∈ eval m c ↔ ∃ u' ∈ eval U (init (encUniv (m, c))), u'.Tape = Tape.mk₁ (encNat (encode c'))`, that equivalence alone does not syntactically state that `U` diverges when `m` diverges (since `[] ≠ encNat _` would rule out a dummy empty-tape halt from the RHS existential even if `U` halted!). `Spec.lean` states the stronger `Part (Tape Γ₀)` identity `U_evalCfg_tape`:
     `(StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c)))).map TM0.Cfg.Tape = (StateTransition.eval (TM0.step m.machine) c).map fun c' ↦ Tape.mk₁ (encNat (Encodable.encode c'))`,
     which simultaneously forces `.Dom` equivalence (diverges iff diverges) and exact full-tape equality on halting runs, plus the membership corollary `U_mem_evalCfg_iff`.
   - *Directive subtlety 2 (prefix collisions and window radius)*: Directive §1 (`T-E(3)`) remarks "a cylinder of length `L = |encNat (encode c')|` isolates `c'`". **Careful**: `encNat 1 = [sym true .cons, sym false .bit1]` (length 2, indices `0, 1`) is a **strict prefix** of `encNat 2 = [sym true .cons, sym false .bit1, sym false .bit0]` (length 3, indices `0, 1, 2`)! Inspecting only cells `0 .. L - 1` does **not** isolate `c'`; one must inspect up to **index `L` inclusive** (for instance the symmetric window `[-L, L]` of radius `L`, which has `2L + 1` cells), because at index `L` `Tape.mk₁ (encNat (encode c'))` has `default` whereas any longer `encNat (encode c'')` has a non-`default` symbol by `default_notMem_encNat`!

5. **Critique of Directive §2.3, §2.9, and §2.10**:
   - *§2.3 Round-trip lemmas*: Universal statements `Encodable.decode (Encodable.encode x) = some x` are immediate instances of `Encodable.encodek` (`Encodable/Basic.lean:56`). While useful in `Spec.lean` to verify diamond-free typeclass synthesis of each scoped `Primcodable` instance, they do **not** test that `encode` computes the intended representation unless paired in Gate G5 with concrete `rfl`/`decide` checks on trailing-blank lists (e.g., `encode (ListBlank.mk [true, false, false]) = encode (ListBlank.mk [true])`).
   - *§2.9 Namespace hygiene*: Combining `open Turing` with `namespace TuringRecursive` without `_root_.` prefixes would place `ListBlank.trim` at `TuringRecursive.ListBlank.trim` (breaking dot-notation `L.trim` on `L : Turing.ListBlank Γ`!) and split `StateTransition`, `Primrec`, and `Turing.TM0` across namespaces contrary to Q2 (Mathlib-PR quality). `Spec.lean` uses `_root_.` on all declarations extending Mathlib types (`StateTransition.*`, `Primrec.list_*`, `Primrec.listBlank_*`, `Primrec.tape_*`, `Turing.ListBlank.*`, `Turing.TM0.*`) while keeping `scoped instance`s and new project types/constants (`TM0Code`, `Γ₀`, `encNat`, `decNat`, `encUniv`, `decUniv`, `UniversalΛ`, `U`) in `TuringRecursive` (with plain `instance`s on project-owned `TM0Code` and `UniversalΛ`).
   - *§2.10 Unused gap items (DROPPED per Q5)*: Directive §2.10 lists `Computable.iterate` and `Primrec.dite` as Mathlib gaps to prove. Because `StateTransition.eval` is a `PFun.fix` proved `Partrec` directly via `Partrec.fix` (`Partrec.lean:769`), neither `Computable.iterate` nor `Primrec.dite` is required by any headline statement; per user decision Q5, they are **dropped as standalone deliverables** and included only if needed internally in M1–M6.

---

## 1. Statement-by-Statement Specification & Review

### 1.1 Milestone `T-B`: Generic `StateTransition` Computability & Iteration

#### `StateTransition.eval_partrec` and `StateTransition.eval_partrec₂`

**(a) Lean text (`spec/Spec.lean:25–37`)**
```lean
-- spec: T-B
theorem _root_.StateTransition.eval_partrec {σ : Type*} [Primcodable σ] {f : σ → Option σ}
    (hf : Computable f) : Partrec (StateTransition.eval f) := by
  sorry

-- spec: T-B
theorem _root_.StateTransition.eval_partrec₂ {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → σ → Option σ} (hf : Computable₂ f) :
    Partrec₂ fun a ↦ StateTransition.eval (f a) := by
  sorry
```

**(b) Mathematical meaning**
Given any constructively countable state space `σ` with primitive recursive Gödel coding (`Primcodable σ`) and any total computable deterministic transition function `f : σ → Option σ` (where `some s'` steps to `s'` and `none` halts), the partial run-to-completion map `StateTransition.eval f : σ → Part σ` returning the unique terminal state reached from an initial state (and diverging if `f` never returns `none`) is partial recursive. Moreover, if `f : α → σ → Option σ` depends computably on an external parameter `a : α` (such as a machine code), then `(a, s) ↦ StateTransition.eval (f a) s` is uniformly partial recursive in both arguments.

**(c) Mathlib source citations**
- `StateTransition.eval` — `Mathlib/Computability/StateTransition.lean:33`
- `PFun.fix` — `Mathlib/Data/PFun.lean:257`
- `Primcodable` — `Mathlib/Computability/Primrec/Basic.lean:131`
- `Partrec`, `Partrec₂`, `Computable`, `Computable₂` — `Mathlib/Computability/Partrec.lean:231, 236, 242, 247`
- `Partrec.fix` — `Mathlib/Computability/Partrec.lean:769`
- `Computable.option_casesOn` — `Mathlib/Computability/Partrec.lean:605`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode*: Stating `eval_partrec` only for `[Fintype σ]` (finite state spaces, where every function is trivially computable and loops are bounded by `Fintype.card σ`) would fail completely on `TM0.Cfg Γ Λ`, whose tape space is infinite! Conversely, requiring `Primrec f` instead of `Computable f` would needlessly weaken the theorem.
- *Why this avoids it*: `σ : Type*` is arbitrary (infinite `TM0.Cfg` included) with only `[Primcodable σ]`, and the hypothesis `Computable f` is minimal (since `f s = none ↔ s ∈ eval f s` when `f s = none`). `StateTransition.eval` is Mathlib's unmodified evaluator.

**(e) Proof plan & estimated lines**
- `eval_partrec` (~10 lines, M1, Carbon/Gemma T1): `StateTransition.eval f` is definitionally `PFun.fix fun s ↦ Part.some <| (f s).elim (Sum.inl s) Sum.inr`. Apply `Partrec.fix` (`Partrec.lean:769`) to `(Computable.option_casesOn hf (Computable.sumInl.comp .id) (Computable.sumInr.comp .snd).to₂).partrec`.
- `eval_partrec₂` (~25 lines, M1, Carbon): Run `eval_partrec` on the product state space `α × σ` with transition `F ⟨a, s⟩ := (f a s).map (a, ·)`, show `StateTransition.Respects (f a) F (fun s p ↦ (a, s) = p)` via `StateTransition.fun_respects` (`StateTransition.lean:236`), and project with `StateTransition.tr_eval'` (`StateTransition.lean:241`) and `Partrec.map`.

---

#### `StateTransition.reaches_iff_exists_iterate`

**(a) Lean text (`spec/Spec.lean:40–45`)**
```lean
-- spec: T-B
theorem _root_.StateTransition.reaches_iff_exists_iterate {σ : Type*} {f : σ → Option σ}
    {a b : σ} :
    StateTransition.Reaches f a b ↔ ∃ n : ℕ, (flip Option.bind f)^[n] (some a) = some b := by
  sorry
```

**(b) Mathematical meaning**
State `b` is reachable from state `a` in zero or more transitions of `f : σ → Option σ` (`StateTransition.Reaches f a b`, defined as the reflexive-transitive closure of `b ∈ f a`) if and only if there exists a step count `n : ℕ` such that iterating the Kleisli-lifted step operator `flip Option.bind f : Option σ → Option σ` `n` times starting from `some a` yields `some b`.

**(c) Mathlib source citations**
- `StateTransition.Reaches` — `Mathlib/Computability/StateTransition.lean:39`
- `StateTransition.EvalsTo` (uses the same `(flip bind f)^[steps]` convention) — `Mathlib/Computability/StateTransition.lean:256–259`
- `Relation.ReflTransGen` — `Mathlib/Logic/Relation.lean:382`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode*: Confusing `Option.bind` argument order (`Option α → (α → Option β) → Option β`) with `Monad.bind` or omitting `flip` would fail to typecheck; iterating a totalized function `s ↦ (f s).getD s` instead of `flip Option.bind f` would conflate halting at `b` (`f b = none`, which stays at `b` forever under `.getD`) with self-loops `f b = some b`!
- *Why this avoids it*: `flip Option.bind f` maps `none ↦ none` (absorbing halt), so `(flip Option.bind f)^[n] (some a) = some b` tracks genuine non-halted `n`-step trajectories and matches Mathlib's `StateTransition.EvalsTo` (`StateTransition.lean:259`).

**(e) Proof plan & estimated lines**
- (~35 lines, M1, Gemma T1 / port of S4TP `FinTM0.reaches_iff_exists_iterate_stepOpt`): `(→)` induct on `ReflTransGen` (`refl` uses `n = 0`; `tail` with `n` steps uses `n + 1` via `Function.iterate_succ_apply'`). `(←)` induct on `n` generalizing `a`, splitting on `f a` via `Function.iterate_succ_apply`.

---

### 1.2 Milestone `E`: List Helpers, `ListBlank.trim`, Scoped `Primcodable` Instances & `Primrec` API

#### `Primrec.list_rdropWhile` and `Primrec.list_dropLast`

**(a) Lean text (`spec/Spec.lean:49–60`)**
```lean
-- spec: E
theorem _root_.Primrec.list_rdropWhile {α : Type*} [Primcodable α] {p : α → Bool}
    (hp : Primrec p) : Primrec (List.rdropWhile p) := by
  sorry

-- spec: E
theorem _root_.Primrec.list_dropLast {α : Type*} [Primcodable α] :
    Primrec (@List.dropLast α) := by
  sorry
```

**(b) Mathematical meaning**
For any `Primcodable` type `α`, dropping elements from the right end of a list while a primitive recursive boolean predicate `p` holds (`List.rdropWhile p`), as well as dropping the final element of a list (`List.dropLast`), are primitive recursive list operations.

**(c) Mathlib source citations**
- `List.rdropWhile` — `Mathlib/Data/List/DropRight.lean:92`
- `Primrec` — `Mathlib/Computability/Primrec/Basic.lean:174`
- `Primrec.list_reverse`, `Primrec.list_length`, `Primrec.list_take`, `Primrec.list_dropWhile` — `Mathlib/Computability/Primrec/List.lean:156, 255, 403, 414`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode*: Adding `[DecidableEq α]` or `[Fintype α]` would restrict generality below Mathlib's `Primrec.list_dropWhile` (`List.lean:414`).
- *Why this avoids it*: Exact signature parity with `Primrec.list_dropWhile` and `Primrec.list_tail` (`List.lean:172`) over arbitrary `{α : Type*} [Primcodable α]`.

**(e) Proof plan & estimated lines**
- `list_rdropWhile` (~3 lines, M2, Gemma T0): `Primrec.list_reverse.comp ((Primrec.list_dropWhile hp).comp Primrec.list_reverse)`.
- `list_dropLast` (~4 lines, M2, Gemma T0): `(Primrec.list_take.comp (Primrec.pred.comp Primrec.list_length) .id).of_eq fun l ↦ l.dropLast_eq_take.symm`.

---

#### `ListBlank.trim` and Canonical Representative Lemmas (`trim_mk`, `mk_trim`, `trim_injective`, `trim_congr`, `rdropWhile_trim`, `listBlank_canonical_primrecPred`)

**(a) Lean text (`spec/Spec.lean:62–110`)**
```lean
-- spec: E
def _root_.Turing.ListBlank.trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (L : ListBlank Γ) : List Γ :=
  L.liftOn (List.rdropWhile (· == default)) <| by
    rintro l _ ⟨n, rfl⟩
    induction n with
    | zero => simp
    | succ n ih =>
      simp [List.replicate_succ', ← List.append_assoc, ih]

-- spec: E
theorem _root_.Turing.ListBlank.trim_mk {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] (l : List Γ) :
    (ListBlank.mk l).trim = l.rdropWhile (· == default) := by
  sorry

-- spec: E
theorem _root_.Turing.ListBlank.mk_trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (L : ListBlank Γ) : ListBlank.mk L.trim = L := by
  sorry

-- spec: E
theorem _root_.Turing.ListBlank.trim_injective {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] :
    Function.Injective (@ListBlank.trim Γ _ _) := by
  sorry

-- spec: E
theorem _root_.Turing.ListBlank.trim_congr {Γ : Type*} [Inhabited Γ]
    (inst₁ inst₂ : DecidableEq Γ) (L : ListBlank Γ) :
    @ListBlank.trim Γ _ inst₁ L = @ListBlank.trim Γ _ inst₂ L := by
  sorry

-- spec: E
theorem _root_.Turing.ListBlank.rdropWhile_trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (L : ListBlank Γ) : L.trim.rdropWhile (· == default) = L.trim := by
  sorry

-- spec: E
theorem listBlank_canonical_primrecPred {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [Primcodable Γ] :
    PrimrecPred fun l : List Γ ↦ l.rdropWhile (· == default) = l := by
  sorry
```

**(b) Mathematical meaning**
`ListBlank Γ` is Mathlib's quotient of `List Γ` modulo appending finitely many trailing `default` (blank) symbols (`BlankRel`). `ListBlank.trim` maps each equivalence class `L : ListBlank Γ` to its unique shortest representative in `List Γ` containing no trailing `default` symbols (`List.rdropWhile (· == default)`). `trim_mk` computes `trim` on `ListBlank.mk l`; `mk_trim` proves `ListBlank.mk` is a left inverse to `trim` (hence `trim_injective`); `trim_congr` proves `trim` is independent of the `[DecidableEq Γ]` instance; `rdropWhile_trim` and `listBlank_canonical_primrecPred` identify the image of `trim` as a primitive recursive subtype of `List Γ`.

**(c) Mathlib source citations**
- `Turing.BlankExtends`, `Turing.BlankRel`, `Turing.ListBlank`, `ListBlank.liftOn`, `ListBlank.mk` — `Mathlib/Computability/TuringMachine/Tape.lean:42, 79, 124, 135, 140`
- `List.rdropWhile`, `List.rdropWhile_concat_pos`, `List.rdropWhile_idempotent`, `List.rdropWhile_append_rtakeWhile`, `List.mem_rtakeWhile_imp` — `Mathlib/Data/List/DropRight.lean:92, 104, 138, 179, 191`
- `PrimrecPred` — `Mathlib/Computability/Primrec/Basic.lean:334`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode*: Defining `ListBlank.trim` via `Quotient.out` (`Classical.choice`) would yield an arbitrary non-computable representative `L.out` for which `mk_trim` and `trim_injective` hold, **but** `trim_mk` fails and `Primrec ListBlank.mk` becomes unprovable (or false for non-computable choice)! Similarly, omitting `trim_congr` would create a subtle mismatch between `instPrimcodableListBlank` (which uses `Encodable.decidableEqOfEncodable Γ` internally) and external callers holding a different `[DecidableEq Γ]`.
- *Why this avoids it*: `ListBlank.trim` is given as an **explicit, computable `sorry`-free definition** via `ListBlank.liftOn (List.rdropWhile (· == default))`, `trim_mk` pins its exact computational behavior on every list, and `trim_congr` bridges any two `DecidableEq Γ` instances.

**(e) Proof plan & estimated lines**
- (~35 lines total, M2, Gemma T0/T1): `trim_mk` is `rfl`; `mk_trim` inducts via `ListBlank.induction_on`, applying `Quotient.sound'` with `List.rdropWhile_append_rtakeWhile` and `List.eq_replicate_length.mpr` + `List.mem_rtakeWhile_imp`; `trim_injective` is `Function.LeftInverse.injective mk_trim`; `trim_congr` uses `Quotient.inductionOn'` + `Subsingleton.elim` on `Decidable` or `beq_iff_eq`; `rdropWhile_trim` uses `Quotient.inductionOn'` + `List.rdropWhile_idempotent`; `listBlank_canonical_primrecPred` composes `Primrec.eq` with `Primrec.list_rdropWhile`.

---

#### Scoped `Primcodable` Instances (`Dir`, `TM0.Stmt Γ`, `ListBlank Γ`, `Tape Γ`, `TM0.Cfg Γ Λ`), `Primrec` Operations, and Round-Trip Lemmas

**(a) Lean text (`spec/Spec.lean:112–283`)**
```lean
-- spec: E
def dirEquivBool : Dir ≃ Bool where
  toFun | .left => false | .right => true
  invFun | false => .left | true => .right
  left_inv d := by cases d <;> rfl
  right_inv b := by cases b <;> rfl

-- spec: E
scoped instance instPrimcodableDir : Primcodable Dir :=
  Primcodable.ofEquiv Bool dirEquivBool

-- spec: E
def stmtEquivSum {Γ : Type*} : TM0.Stmt Γ ≃ Dir ⊕ Γ where
  toFun | .move d => Sum.inl d | .write a => Sum.inr a
  invFun | Sum.inl d => .move d | Sum.inr a => .write a
  left_inv s := by cases s <;> rfl
  right_inv x := by cases x <;> rfl

-- spec: E
scoped instance instDecidableEqStmt {Γ : Type*} [DecidableEq Γ] : DecidableEq (TM0.Stmt Γ) :=
  Equiv.decidableEq stmtEquivSum

-- spec: E
scoped instance instPrimcodableStmt {Γ : Type*} [Primcodable Γ] : Primcodable (TM0.Stmt Γ) :=
  Primcodable.ofEquiv (Dir ⊕ Γ) stmtEquivSum

-- spec: E
def listBlankEquivCanonical {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] :
    ListBlank Γ ≃ { l : List Γ // l.rdropWhile (· == default) = l } where
  toFun L := ⟨L.trim, L.rdropWhile_trim⟩
  invFun s := ListBlank.mk s.1
  left_inv := ListBlank.mk_trim
  right_inv s := Subtype.ext ((ListBlank.trim_mk s.1).trans s.2)

-- spec: E
scoped instance instPrimcodableListBlank {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primcodable (ListBlank Γ) :=
  letI : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ
  letI : Primcodable { l : List Γ // l.rdropWhile (· == default) = l } :=
    Primcodable.subtype listBlank_canonical_primrecPred
  Primcodable.ofEquiv { l : List Γ // l.rdropWhile (· == default) = l } listBlankEquivCanonical

-- spec: E
def tapeEquivProd {Γ : Type*} [Inhabited Γ] :
    Tape Γ ≃ Γ × ListBlank Γ × ListBlank Γ where
  toFun T := (T.head, T.left, T.right)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv T := by cases T; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

-- spec: E
scoped instance instPrimcodableTape {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primcodable (Tape Γ) :=
  Primcodable.ofEquiv (Γ × ListBlank Γ × ListBlank Γ) tapeEquivProd

-- spec: E
def cfgEquivProd {Γ Λ : Type*} [Inhabited Γ] :
    TM0.Cfg Γ Λ ≃ Λ × Tape Γ where
  toFun c := (c.q, c.Tape)
  invFun p := ⟨p.1, p.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl

-- spec: E
scoped instance instPrimcodableCfg {Γ Λ : Type*} [Inhabited Γ] [Primcodable Γ] [Primcodable Λ] :
    Primcodable (TM0.Cfg Γ Λ) :=
  Primcodable.ofEquiv (Λ × Tape Γ) cfgEquivProd

-- spec: E  (Primrec operations on ListBlank and Tape — in `_root_.Primrec` per Q2)
theorem _root_.Primrec.listBlank_mk {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (ListBlank.mk : List Γ → ListBlank Γ) := by sorry
theorem _root_.Primrec.listBlank_trim {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [Primcodable Γ] :
    Primrec (ListBlank.trim : ListBlank Γ → List Γ) := by sorry
theorem _root_.Primrec.listBlank_head {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (ListBlank.head : ListBlank Γ → Γ) := by sorry
theorem _root_.Primrec.listBlank_tail {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (ListBlank.tail : ListBlank Γ → ListBlank Γ) := by sorry
theorem _root_.Primrec.listBlank_cons {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (ListBlank.cons : Γ → ListBlank Γ → ListBlank Γ) := by sorry
theorem _root_.Primrec.listBlank_nth {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (ListBlank.nth : ListBlank Γ → ℕ → Γ) := by sorry
theorem _root_.Primrec.tape_move {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.move : Dir → Tape Γ → Tape Γ) := by sorry
theorem _root_.Primrec.tape_write {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.write : Γ → Tape Γ → Tape Γ) := by sorry
theorem _root_.Primrec.tape_mk₁ {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (Tape.mk₁ : List Γ → Tape Γ) := by sorry
theorem _root_.Primrec.tape_mk₂ {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.mk₂ : List Γ → List Γ → Tape Γ) := by sorry
theorem _root_.Primrec.tape_nth {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec₂ (Tape.nth : Tape Γ → ℤ → Γ) := by sorry
theorem _root_.Primrec.tape_right₀ {Γ : Type*} [Inhabited Γ] [Primcodable Γ] :
    Primrec (Tape.right₀ : Tape Γ → ListBlank Γ) := by sorry

-- spec: E  (Round-trip statements)
theorem decode_encode_dir (d : Dir) : Encodable.decode (Encodable.encode d) = some d := by sorry
theorem decode_encode_stmt {Γ : Type*} [Primcodable Γ] (s : TM0.Stmt Γ) :
    Encodable.decode (Encodable.encode s) = some s := by sorry
theorem decode_encode_listBlank {Γ : Type*} [Inhabited Γ] [Primcodable Γ] (L : ListBlank Γ) :
    Encodable.decode (Encodable.encode L) = some L := by sorry
theorem decode_encode_tape {Γ : Type*} [Inhabited Γ] [Primcodable Γ] (T : Tape Γ) :
    Encodable.decode (Encodable.encode T) = some T := by sorry
theorem decode_encode_cfg {Γ Λ : Type*} [Inhabited Γ] [Primcodable Γ] [Primcodable Λ]
    (c : TM0.Cfg Γ Λ) : Encodable.decode (Encodable.encode c) = some c := by sorry
```

**(b) Mathematical meaning**
Constructs explicit, computable Gödel encodings (`Primcodable`, scoped to `TuringRecursive`) for directions `Dir`, `TM0` instructions `TM0.Stmt Γ`, quotient half-tapes `ListBlank Γ` (via the canonical trailing-blank-free subtype `{l : List Γ // l.rdropWhile (· == default) = l}`), two-sided tapes `Tape Γ`, and machine configurations `TM0.Cfg Γ Λ`, requiring only `[Inhabited Γ] [Primcodable Γ]` (and `[Primcodable Λ]`). Under these encodings, all standard `ListBlank` (`mk`, `trim`, `head`, `tail`, `cons`, `nth`) and `Tape` (`move`, `write`, `mk₁`, `mk₂`, `nth`, `right₀`) operations are primitive recursive, and `decode ∘ encode = some` holds for each instance.

**(c) Mathlib source citations**
- `Turing.Dir`, `Turing.Tape`, `Tape.right₀`, `Tape.move`, `Tape.mk'`, `Tape.mk₂`, `Tape.mk₁`, `Tape.nth`, `Tape.write` — `Mathlib/Computability/TuringMachine/Tape.lean:407, 420, 430, 435, 450, 488, 493, 498, 541`
- `ListBlank.head`, `ListBlank.tail`, `ListBlank.cons`, `ListBlank.nth` — `Mathlib/Computability/TuringMachine/Tape.lean:149, 162, 176, 211`
- `Turing.TM0.Stmt`, `Turing.TM0.Cfg` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:116, 142`
- `Encodable.encode`, `Encodable.decode`, `Encodable.encodek`, `Encodable.decidableEqOfEncodable` — `Mathlib/Logic/Encodable/Basic.lean:50–56, 85`
- `Denumerable.int` (furnishes `Primcodable ℤ` for `tape_nth`) — `Mathlib/Basic/Denumerable.lean:158`
- `Primcodable.ofEquiv`, `Primcodable.bool`, `Primcodable.prod`, `Primcodable.sum`, `Primcodable.subtype`, `Primrec₂` — `Mathlib/Computability/Primrec/Basic.lean:143, 164, 268, 328, 750, 809`
- `Primcodable.list` — `Mathlib/Computability/Primrec/List.lean:108`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode 1 (hidden `sorry` data)*: If `instPrimcodableListBlank` were a `sorry`-bodied instance, `encode` and `decode` would be opaque terms, making `Primrec` statements vacuous or mutually inconsistent. Here **every single `Primcodable` instance is a real computable `Primcodable.ofEquiv` construction** whose `encode L` is definitionally `Encodable.encode L.trim`.
- *Failure mode 2 (`DecidableEq` diamond)*: Including `[DecidableEq Γ]` as an instance parameter of `instPrimcodableListBlank` would cause typeclass diamonds whenever `[Primcodable Γ]` and `[Fintype Γ]`/`Classical.decEq` coexist. Using `letI : DecidableEq Γ := Encodable.decidableEqOfEncodable Γ` *inside* `instPrimcodableListBlank` eliminates the parameter completely, while `trim_congr` ensures `listBlank_trim` works for *any* external `[DecidableEq Γ]`.
- *Failure mode 3 (vacuous round-trip test)*: As noted in §0.5, `decode_encode_*` is proved by `Encodable.encodek` for any `Encodable` instance; M2's Gate G5 test file must add concrete `rfl`/`decide` quotient-collapse assertions (`encode (ListBlank.mk [a, default]) = encode (ListBlank.mk [a])`).

**(e) Proof plan & estimated lines**
- (~350–550 lines total, M2, high Gemma T0/T1 share): Prove the characterization `Primrec f ↔ Primrec (fun x ↦ (f x).trim)` from `Primrec.of_equiv_iff` (`Primrec/Basic.lean:250`) and `Primrec.subtype_val_iff` (`Primrec/Basic.lean:855`). Then each `ListBlank` operation reduces to a list identity (`(ListBlank.mk l).trim = l.rdropWhile ...`, `L.head = L.trim.headI`, `L.tail.trim = L.trim.tail`, `(L.cons a).trim = (a :: L.trim).rdropWhile ...`, `L.nth n = L.trim.getI n`), and each `Tape` operation reduces via `tapeEquivProd` to product projections, `Primrec.cond` on `dirEquivBool`, and integer sign splitting via `Denumerable.int` (`Equiv.intEquivNat`). Round-trip lemmas are 1-liners (`Encodable.encodek _`).

---

### 1.3 Milestone `T-A` & `T-A'`: Fixed-Machine `TM0` Computability

#### `TM0.step_primrec_of_primrec`, `TM0.step_primrec`, `TM0.evalCfg_partrec`, `TM0.eval_partrec`, and `TM0.exists_code_eval` (`T-A'`)

**(a) Lean text (`spec/Spec.lean:289–332`)**
```lean
-- spec: T-A
theorem _root_.Turing.TM0.step_primrec_of_primrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    {M : TM0.Machine Γ Λ} (hM : Primrec₂ M) :
    Primrec (TM0.step M) := by
  sorry

-- spec: T-A
theorem _root_.Turing.TM0.step_primrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    Primrec (TM0.step M) := by
  sorry

-- spec: T-A
theorem _root_.Turing.TM0.evalCfg_partrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    Partrec (StateTransition.eval (TM0.step M)) := by
  sorry

-- spec: T-A
theorem _root_.Turing.TM0.eval_partrec
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    Partrec (TM0.eval M) := by
  sorry

-- spec: T-A'
theorem _root_.Turing.TM0.exists_code_eval
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ]
    [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) :
    ∃ c : Nat.Partrec.Code, ∀ l,
      c.eval (Encodable.encode l) = (TM0.eval M l).map Encodable.encode := by
  sorry
```

**(b) Mathematical meaning**
`step_primrec_of_primrec` shows that for *any* Post–Turing machine `M : TM0.Machine Γ Λ` (even with infinitely many states or symbols) whose transition table `M : Λ → Γ → Option (Λ × TM0.Stmt Γ)` is binary primitive recursive, its one-step configuration transition `TM0.step M : TM0.Cfg Γ Λ → Option (TM0.Cfg Γ Λ)` is primitive recursive. Specializing to finite `Γ` and `Λ` (where *every* transition function is automatically primitive recursive without needing `DecidableEq`), `step_primrec` proves `Primrec (TM0.step M)`, `evalCfg_partrec` proves full configuration evaluation `StateTransition.eval (TM0.step M)` is partial recursive, `eval_partrec` proves Mathlib's list-to-`ListBlank` evaluator `TM0.eval M` is partial recursive, and `exists_code_eval` (`T-A'`) gives the classical Kleene normal form: a concrete `Nat.Partrec.Code` computing `TM0.eval M` on `Encodable.encode`d input lists.

**(c) Mathlib source citations**
- `Turing.TM0.Machine`, `Turing.TM0.step`, `Turing.TM0.init`, `Turing.TM0.eval` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:133, 157, 167, 171`
- `StateTransition.eval` — `Mathlib/Computability/StateTransition.lean:33`
- `Primrec₂.uncurry`, `Primrec.dom_finite` — `Mathlib/Computability/Primrec/Basic.lean:383, 678`
- `Nat.Partrec.Code`, `Nat.Partrec.Code.eval`, `Nat.Partrec.Code.exists_code` — `Mathlib/Computability/PartrecCode.lean:74, 458, 530`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode 1 (baking in `Fintype.equivFin` or `DecidableEq`)*: Requiring `M : TM0.Machine (Fin m) (Fin n)` or `[DecidableEq Λ]` would fail directly on Mathlib's `restrictSupportedTM0` machines whose state types are subtypes of `TM1to0.Λ'` (which carry functions in their constructors and lack constructive `DecidableEq`). Quantifying over arbitrary `[Primcodable Γ] [Primcodable Λ] [Finite Γ] [Finite Λ]` avoids all choice/decidability restrictions (§2.4).
- *Failure mode 2 (existential encoding in `T-A'`)*: If `T-A'` quantified existentially over an encoding `∃ enc, ∃ c, ...`, a degenerate non-computable `enc` encoding halting into bit 0 would make `c` trivial. Instead, `T-A'` uses the fixed typeclass `Encodable.encode` from `[Primcodable (List Γ)]` and `instPrimcodableListBlank`.

**(e) Proof plan & estimated lines**
- (~120–180 lines total, M3, Gemma T1 + Carbon):
  - `step_primrec_of_primrec` (~45 lines): Decompose `c : TM0.Cfg Γ Λ` via `cfgEquivProd` and `tapeEquivProd`, apply `Primrec.option_map` to `hM.comp cfg_q tape_head`, and dispatch `TM0.Stmt` via `stmtEquivSum` + `Primrec.sumCasesOn` to `tape_move` and `tape_write`.
  - `step_primrec` (~10 lines): `haveI : Finite (Λ × Γ) := inferInstance`; apply `step_primrec_of_primrec (Primrec₂.uncurry.mp (Primrec.dom_finite (Function.uncurry M)))`.
  - `evalCfg_partrec` (~5 lines): `StateTransition.eval_partrec (TM0.step_primrec M).to_comp`.
  - `eval_partrec` (~15 lines): Unfold `TM0.eval`, compose `evalCfg_partrec` with `Primrec` of `TM0.init` (`tape_mk₁` + `.const default`), and apply `Partrec.map` (`Partrec.lean:410`) with `tape_right₀`.
  - `exists_code_eval` (~15 lines): Unfold `Partrec (TM0.eval M)` (`Partrec.lean:231`), obtain `c` from `Nat.Partrec.Code.exists_code.mp` (`PartrecCode.lean:530`), evaluate at `Encodable.encode l`, and simplify via `Encodable.encodek` (`Encodable/Basic.lean:56`).

---

### 1.4 Milestone `T-C`: Uniform `TM0Code` over `ℕ` & Pointed Relabeling

#### `TM0Code`, `TM0Code.machine`, `instPrimcodableTM0Code`, `decode_encode_tm0Code`, `TM0Code.step_primrec`, and `TM0Code.eval_partrec`

**(a) Lean text (`spec/Spec.lean:340–380`)**
```lean
-- spec: T-C
structure TM0Code where
  table : List (List (Option (ℕ × TM0.Stmt ℕ)))
  deriving DecidableEq, Inhabited

-- spec: T-C
def TM0Code.machine (m : TM0Code) : TM0.Machine ℕ ℕ :=
  fun q a ↦ (m.table[q]?).bind fun row ↦ (row[a]?).join

-- spec: T-C
def tm0CodeEquivList : TM0Code ≃ List (List (Option (ℕ × TM0.Stmt ℕ))) where
  toFun m := m.table
  invFun t := ⟨t⟩
  left_inv m := by cases m; rfl
  right_inv _ := rfl

-- spec: T-C
instance instPrimcodableTM0Code : Primcodable TM0Code :=
  Primcodable.ofEquiv (List (List (Option (ℕ × TM0.Stmt ℕ)))) tm0CodeEquivList

-- spec: T-C
theorem decode_encode_tm0Code (m : TM0Code) :
    Encodable.decode (Encodable.encode m) = some m := by
  sorry

-- spec: T-C
theorem TM0Code.step_primrec :
    Primrec₂ fun (m : TM0Code) (c : TM0.Cfg ℕ ℕ) ↦ TM0.step m.machine c := by
  sorry

-- spec: T-C
theorem TM0Code.eval_partrec :
    Partrec₂ fun (m : TM0Code) (c : TM0.Cfg ℕ ℕ) ↦
      StateTransition.eval (TM0.step m.machine) c := by
  sorry
```

**(b) Mathematical meaning**
`TM0Code` is a concrete syntax-tree / transition-table representation of finite Post–Turing machines over state and symbol type `ℕ` (where `0 = default` serves as both the blank tape symbol and the initial state). Entry `(q, a)` is looked up as `(m.table[q]?).bind fun row ↦ (row[a]?).join`, returning `none` (halt) whenever `q` or `a` lies outside the table bounds; hence *every* `m : TM0Code` denotes a well-defined `TM0.Machine ℕ ℕ`. Under `instPrimcodableTM0Code`, the uniform interpreter `(m, c) ↦ TM0.step m.machine c` is binary primitive recursive (`step_primrec`), and uniform run-to-completion `(m, c) ↦ StateTransition.eval (TM0.step m.machine) c` is binary partial recursive (`eval_partrec`).

**(c) Mathlib source citations**
- `Turing.TM0.Stmt`, `Turing.TM0.Machine`, `Turing.TM0.Cfg`, `Turing.TM0.step` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:116, 133, 142, 157`
- `StateTransition.eval` — `Mathlib/Computability/StateTransition.lean:33`
- `Primcodable.ofEquiv`, `Primrec.option_bind`, `Primrec.option_map` — `Mathlib/Computability/Primrec/Basic.lean:143, 554, 561`
- `Primrec.list_getElem?` — `Mathlib/Computability/Primrec/List.lean:187`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode 1 (dependent / partial code validity)*: Defining codes as dependent bundles `Σ n m, Fin n → Fin m → ...` or restricting to well-formed rectangular tables with a non-trivial validity invariant would complicate Gödel numbering or allow out-of-range symbols written on the initial tape `c : TM0.Cfg ℕ ℕ` to wrap modulo `m` instead of halting. With `(m.table[q]?).bind fun row ↦ (row[a]?).join`, every `TM0Code` is total on `ℕ × ℕ` and halts cleanly out of range.
- *Failure mode 2 (opaque `machine`)*: Both `TM0Code` and `TM0Code.machine` are concrete computable definitions (zero `sorry`).

**(e) Proof plan & estimated lines**
- (~60–90 lines, M4, Gemma T0/T1): Prove `TM0Code.machine_primrec : Primrec fun p : TM0Code × ℕ × ℕ ↦ p.1.machine p.2.1 p.2.2` using `Primrec.of_equiv` (`tm0CodeEquivList`), `Primrec.list_getElem?`, and `Primrec.option_bind`. Combine with `tape_move` and `tape_write` (exact same structure as `TM0.step_primrec_of_primrec`) to get `TM0Code.step_primrec`. Deduce `TM0Code.eval_partrec` in 2 lines from `StateTransition.eval_partrec₂ TM0Code.step_primrec.to_comp`.

---

#### `TM0Code.exists_relabeling`

**(a) Lean text (`spec/Spec.lean:386–396`)**
```lean
-- spec: T-C
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
  sorry
```

**(b) Mathematical meaning**
Every Post–Turing machine `M : TM0.Machine Γ Λ` over arbitrary finite inhabited alphabet `Γ` and state space `Λ` (in any universe!) is isomorphic, via **injective** pointed encodings `f : PointedMap Γ ℕ` (`f default = 0`) and `g : PointedMap Λ ℕ` (`g default = 0`), to the machine `m.machine` of a concrete tabular code `m : TM0Code`, commuting with both configuration-level evaluation `StateTransition.eval` and list-level evaluation `TM0.eval`.

**(c) Mathlib source citations**
- `Turing.PointedMap`, `Turing.ListBlank.map`, `Turing.Tape.map` — `Mathlib/Computability/TuringMachine/Tape.lean:275, 303, 564`
- `Turing.TM0.Cfg.map`, `Turing.TM0.Machine.map`, `Turing.TM0.Machine.map_step`, `Turing.TM0.map_init` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:212, 220, 223, 236`
- `StateTransition.Respects`, `StateTransition.fun_respects`, `StateTransition.tr_eval'` — `Mathlib/Computability/StateTransition.lean:151, 236, 241`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode 1 (missing injectivity — CAUGHT AND FIXED)*: As proved in §0.1, omitting `Function.Injective f ∧ Function.Injective g` allows `f = const 0`, `g = const 0`, `m = ⟨[]⟩` to satisfy both simulation equations on *every* total halting machine `M`, collapsing distinct outputs to `0`! Requiring `Function.Injective f ∧ Function.Injective g` makes `Cfg.map f g` and `ListBlank.map f` injective, completely ruling out collapse exploits.
- *Failure mode 2 (unpointed `g : Λ → ℕ`)*: If `g` were a bare function `Λ → ℕ` without `g default = 0`, `(TM0.init l).map f g = ⟨g default, Tape.mk₁ (l.map f)⟩` would not equal `TM0.init (l.map f) = ⟨0, Tape.mk₁ (l.map f)⟩`, breaking the `TM0.eval` simulation equation. Making `g : PointedMap Λ ℕ` enables `TM0.map_init` (`PostTuringMachine.lean:236`).
- *Failure mode 3 (`m.machine = M.map ...` false global equality)*: Globally on `ℕ × ℕ`, `m.machine` returns `none` for `q ≥ |Λ|` or `a ≥ |Γ|`, whereas `M.map f f₂ g g₂` maps out-of-range indices to `default` and runs `M default default`. However, on configurations of the form `c.map f g`, every state and tape cell lies in `Set.range g` and `Set.range f`, where `m.machine` and `M.map` agree identically!

**(e) Proof plan & estimated lines**
- (~180–280 lines, M4, Carbon + Gemma T1 helpers): From `[Finite Γ] [Inhabited Γ]`, obtain `nΓ > 0` and `eΓ : Γ ≃ Fin nΓ` with `eΓ default = ⟨0, _⟩` (compose `Finite.exists_equiv_fin` with `Equiv.swap (e default) ⟨0, _⟩`); analogously obtain `eΛ : Λ ≃ Fin nΛ` with `eΛ default = ⟨0, _⟩`. Define `f := ⟨fun a ↦ (eΓ a).1, ...⟩`, `g := ⟨fun q ↦ (eΛ q).1, ...⟩` (both injective via `Fin.val_injective.comp e.injective`), left inverses `f₂ : PointedMap ℕ Γ` and `g₂ : ℕ → Λ`, and `m := ⟨List.ofFn fun i : Fin nΛ ↦ List.ofFn fun j : Fin nΓ ↦ (M (eΛ.symm i) (eΓ.symm j)).map (Prod.map g (TM0.Stmt.map f))⟩`. Show `TM0.step m.machine (c.map f g) = (TM0.step M c).map (TM0.Cfg.map f g)` by `TM0.Machine.map_step` (`S = Set.univ`) plus boundedness `(c.map f g).Tape.1 ∈ Set.range f` (`Tape.map_fst`), apply `StateTransition.tr_eval'` (`StateTransition.lean:241`), and deduce the `TM0.eval` clause via `TM0.map_init` and `Tape.map_right₀`.

---

### 1.5 Milestone `T-D`: Fixed Alphabet `Γ₀`, `encNat` / `decNat`, & Church–Turing Equivalence

#### `PartrecToTM2.K'` Finiteness, `Γ₀`, `encNat`, `decNat`, and Encoding Properties

**(a) Lean text (`spec/Spec.lean:402–502`)**
```lean
-- spec: T-D
def kPrimeEquivFin4 : PartrecToTM2.K' ≃ Fin 4 where ... -- explicit 4-way match, 0 sorry

-- spec: T-D
scoped instance instFintypeK' : Fintype PartrecToTM2.K' :=
  Fintype.ofEquiv (Fin 4) kPrimeEquivFin4.symm

-- spec: T-D
def gammaPrimeEquivFin4 : PartrecToTM2.Γ' ≃ Fin 4 where ... -- explicit 4-way match, 0 sorry

-- spec: T-D
abbrev Γ₀ : Type :=
  TM2to1.Γ' PartrecToTM2.K' (fun _ ↦ PartrecToTM2.Γ')

-- spec: T-D
scoped instance instDecidableEqΓ₀ : DecidableEq Γ₀ :=
  inferInstanceAs (DecidableEq (Bool × (PartrecToTM2.K' → Option PartrecToTM2.Γ')))

-- spec: T-D
def gamma0Equiv : Γ₀ ≃ Bool × (Fin 4 → Option (Fin 4)) :=
  Equiv.prodCongr (Equiv.refl Bool)
    (Equiv.arrowCongr kPrimeEquivFin4 (Equiv.optionCongr gammaPrimeEquivFin4))

-- spec: T-D
scoped instance instPrimcodableΓ₀ : Primcodable Γ₀ :=
  Primcodable.ofEquiv (Bool × (Fin 4 → Option (Fin 4))) gamma0Equiv

-- spec: T-D
theorem decode_encode_Γ₀ (a : Γ₀) : Encodable.decode (Encodable.encode a) = some a := by sorry

-- spec: T-D
def encNat (n : ℕ) : List Γ₀ :=
  TM2to1.trInit (Γ := fun _ ↦ PartrecToTM2.Γ') PartrecToTM2.K'.main (PartrecToTM2.trList [n])

-- spec: T-D
def decNat (L : ListBlank Γ₀) : ℕ :=
  L.trim.tail.foldl (fun acc x ↦
    match x.2 PartrecToTM2.K'.main with
    | some .bit0 => 2 * acc
    | some .bit1 => 2 * acc + 1
    | _ => acc) 0

-- spec: T-D
theorem default_notMem_encNat (n : ℕ) : (default : Γ₀) ∉ encNat n := by sorry
theorem primrec_encNat : Primrec encNat := by sorry
theorem primrec_decNat : Primrec decNat := by sorry
theorem decNat_encNat (n : ℕ) : decNat (ListBlank.mk (encNat n)) = n := by sorry
```

**(b) Mathematical meaning**
Fixes the concrete 1250-symbol finite tape alphabet `Γ₀ = Bool × (PartrecToTM2.K' → Option PartrecToTM2.Γ')` of Mathlib's compiled `PartrecToTM2` stack machine (with blank `default = (false, fun _ ↦ none)`), equips `PartrecToTM2.K'` with `Fintype` and `Γ₀` with computable `DecidableEq` and `Primcodable`, and defines the concrete named natural-number tape representation `encNat n` (the stack-bottom marker `(true, main ↦ some .cons)` followed by the big-endian binary digits of `n` on `.main` with `(false, ...)`) together with its explicit Horner-scheme left inverse `decNat : ListBlank Γ₀ → ℕ`. Every symbol in `encNat n` carries `some _ ≠ none` on `.main`, so `default ∉ encNat n`.

**(c) Mathlib source citations**
- `Turing.PartrecToTM2.Γ'`, `Turing.PartrecToTM2.K'`, `Turing.PartrecToTM2.trNat`, `Turing.PartrecToTM2.trList` — `Mathlib/Computability/TuringMachine/ToPartrec.lean:159, 173, 443, 463`
- `Turing.TM2to1.Γ'`, `TM2to1.Γ'.inhabited`, `TM2to1.Γ'.fintype`, `Turing.TM2to1.trInit` — `Mathlib/Computability/TuringMachine/StackTuringMachine.lean:347, 352, 355, 486`
- `Fintype.ofEquiv` — `Mathlib/Data/Fintype/OfMap.lean:76`
- `Primcodable.finArrow` — `Mathlib/Computability/Primrec/List.lean:543`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode*: Leaving `encNat` or `decNat` existentially quantified in `T-D` (`∃ enc, ...`) would allow `enc` to precompute arbitrary recursive functions or fail to match Mathlib's `PartrecToTM2` conventions; conversely, if `encNat n` ended with `default`, `ListBlank.mk (encNat n)` would strip trailing symbols and corrupt `decNat`.
- *Why this avoids it*: Both `encNat` and `decNat` are concrete, named, `sorry`-free definitions; `default_notMem_encNat` guarantees `(ListBlank.mk (encNat n)).trim = encNat n`, and `decNat_encNat` proves exact left-invertibility (which also implies `Function.Injective (ListBlank.mk ∘ encNat)`!).

**(e) Proof plan & estimated lines**
- (~120–180 lines, M5, Gemma T1 + Carbon):
  - `default_notMem_encNat` (~15 lines): Unfold `encNat` and `TM2to1.trInit`; `trList [n] = trNat n ++ [.cons]` is nonempty, so every `x ∈ encNat n` has `x.2 .main ∈ Set.range some`, contradicting `(default : Γ₀).2 .main = none`.
  - `primrec_encNat` (~55 lines, port of S4TP `UndecidabilityAndTransfer.lean:538–602`): Express `trNat n` as `n`-fold iteration `(succΓ')^[n] []` via `Primrec.nat_iterate`, then apply `Primrec.list_append`, `Primrec.list_reverse`, and `Primrec.list_map`.
  - `primrec_decNat` (~20 lines): Compose `listBlank_trim`, `Primrec.list_tail`, and `Primrec.list_foldl` (`Primrec/List.lean:151`).
  - `decNat_encNat` (~45 lines): Rewrite `(ListBlank.mk (encNat n)).trim = encNat n` via `rdropWhile_eq_self_iff` + `default_notMem_encNat`, simplify `(encNat n).tail` to `(trNat n).reverse.map ...`, and induct on `PosNum` / `Num` to check big-endian Horner evaluation recovers `n`.

---

#### `nat_partrec_iff_exists_tm0` (Church–Turing Equivalence for `TM0`)

**(a) Lean text (`spec/Spec.lean:508–513`)**
```lean
-- spec: T-D
theorem nat_partrec_iff_exists_tm0 {f : ℕ →. ℕ} :
    Nat.Partrec f ↔
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (_ : Inhabited Λ)
        (M : TM0.Machine Γ₀ Λ),
        ∀ n : ℕ, TM0.eval M (encNat n) = (f n).map (ListBlank.mk ∘ encNat) := by
  sorry
```

**(b) Mathematical meaning**
A partial numerical function `f : ℕ →. ℕ` is partial recursive (`Nat.Partrec f`) if and only if there exists a finite-state Post–Turing machine `M : TM0.Machine Γ₀ Λ` over the fixed alphabet `Γ₀` (with finite, decidably-equal, inhabited state type `Λ : Type`) such that for every `n : ℕ`, running `M` on `encNat n` halts if and only if `f n` is defined, and when `m ∈ f n` its output half-tape `TM0.eval M (encNat n)` equals `ListBlank.mk (encNat m)`.

**(c) Mathlib source citations**
- `Nat.Partrec` — `Mathlib/Computability/Partrec.lean:157`
- `Turing.ToPartrec.Code.exists_code` — `Mathlib/Computability/TuringMachine/Config.lean:272`
- `Turing.PartrecToTM2.tr`, `PartrecToTM2.halt`, `PartrecToTM2.init`, `PartrecToTM2.tr_eval`, `PartrecToTM2.codeSupp`, `PartrecToTM2.tr_supports` — `Mathlib/Computability/TuringMachine/ToPartrec.lean:301, 537, 934, 942, 1042, 1274`
- `Turing.TM2to1.tr`, `TM2to1.TrCfg`, `TM2to1.tr_respects`, `TM2to1.trCfg_init`, `TM2to1.trSupp`, `TM2to1.tr_supports` — `Mathlib/Computability/TuringMachine/StackTuringMachine.lean:624, 632, 687, 709, 753, 757`
- `Turing.TM1to0.tr`, `TM1to0.tr_eval`, `TM1to0.trStmts`, `TM1to0.tr_supports` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:515, 540, 550, 556`
- `Turing.TM0.eval`, `Turing.TM0.Supports` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:171, 181`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode 1 (omitting `[Fintype Λ]`)*: Without `[Fintype Λ]`, *every* partial function `f : ℕ →. ℕ` (including the halting oracle!) is trivially "computed" by an infinite-state `TM0` machine that reads `n` into its `ℕ`-indexed state space in `O(|encNat n|)` steps and then transitions directly to a state encoding the uncomputable value `f n`! Requiring `[Fintype Λ]` is the entire mathematical content of `(⇐)`.
- *Failure mode 2 (using `TM2to1.tr_eval` blindly in `(⇒)`)*: `TM2to1.tr_eval` (`StackTuringMachine.lean:734`) existentially forgets that stacks `.rev`, `.aux`, and `.stack` are `[]` in `PartrecToTM2.halt [m]`, which is insufficient to conclude `L₁ = ListBlank.mk (encNat m)`. One must apply `StateTransition.tr_eval` / `tr_eval_rev` directly to `TM2to1.tr_respects` (`StackTuringMachine.lean:687`), where `TrCfg` (`L632–635`) gives `Tape.mk' ∅ (addBottom L)` with `L` uniquely determined across all 4 stacks!
- *Failure mode 3 (universe mismatch)*: Because `Γ₀ : Type` lives in `Type 0`, quantifying `Λ : Type` in `Type 0` avoids universe-ulift clutter while capturing every finite state space up to bijection (`Fintype.equivFin`).

**(e) Proof plan & estimated lines**
- (~280–400 lines, M5, Carbon):
  - `(⇒)` (~220 lines): Obtain `c : ToPartrec.Code` via `Nat.Partrec'.part_iff₁` + `Code.exists_code`. Set `letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal c .halt⟩` so `TM2.init .main (trList [n]) = PartrecToTM2.init c [n]`. Use `PartrecToTM2.tr_eval c [n]` + `StateTransition.tr_eval` / `tr_eval_rev` on `TM2to1.tr_respects` and `ListBlank.ext` (`proj_map_nth`) to prove `StateTransition.eval (TM1.step tm1) (TM1.init (encNat n))` has halting tape `Tape.mk' ∅ (ListBlank.mk (encNat m)) = Tape.mk₁ (encNat m)`. Chain `TM1to0.tr_eval` (or `TM1to0.tr_respects` for full tape!) and restrict the state space to the finite support subtype `↥S₀` (`S₀ = TM1to0.trStmts tm1 (TM2to1.trSupp _ (PartrecToTM2.codeSupp c .halt))`) via `restrictSupportedTM0` (adapted from S4TP `UndecidabilityAndTransfer.lean:62–100`).
  - `(⇐)` (~40 lines): Given finite `Λ` with `[Fintype Λ] [DecidableEq Λ] [Inhabited Λ]`, construct `Primcodable Λ` via `Primcodable.ofEquiv (Fin (Fintype.card Λ)) (Fintype.equivFin Λ)`. By `TM0.eval_partrec M` (`T-A`), `primrec_encNat`, and `primrec_decNat`, `(fun n ↦ (TM0.eval M (encNat n)).map decNat)` is `Partrec`, and equals `f` by `decNat_encNat`!

---

### 1.6 Milestone `T-E`: Halting Undecidability, Compiler, & Windowed Universal `TM0`

#### `T-E(1)`: `TM0Code.halting_re` and `TM0Code.halting_not_computable`

**(a) Lean text (`spec/Spec.lean:519–530`)**
```lean
-- spec: T-E(1)
theorem TM0Code.halting_re :
    REPred fun p : TM0Code × TM0.Cfg ℕ ℕ ↦
      (StateTransition.eval (TM0.step p.1.machine) p.2).Dom := by
  sorry

-- spec: T-E(1)
theorem TM0Code.halting_not_computable :
    ¬ ComputablePred fun p : TM0Code × TM0.Cfg ℕ ℕ ↦
      (StateTransition.eval (TM0.step p.1.machine) p.2).Dom := by
  sorry
```

**(b) Mathematical meaning**
The uniform Post–Turing halting problem — deciding whether a coded machine `m : TM0Code` eventually halts (`none`) when started from configuration `c : TM0.Cfg ℕ ℕ` — is recursively enumerable (`REPred`) but algorithmically undecidable (`¬ ComputablePred`).

**(c) Mathlib source citations**
- `ComputablePred`, `REPred`, `Partrec.dom_re` — `Mathlib/Computability/RE.lean:129, 157, 164`
- `ComputablePred.halting_problem` — `Mathlib/Computability/Halting.lean:64`
- `StateTransition.eval` — `Mathlib/Computability/StateTransition.lean:33`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode*: If `instPrimcodableTM0Code` or `instPrimcodableCfg` smuggled a halting oracle into `Encodable.encode`, `halting_re` could hold trivially while `halting_not_computable` would actually be **false**! Proving **both** `REPred` and `¬ ComputablePred` serves as a hard semantic anti-vacuity lock (§6 G5): neither `TM0Code` nor `instPrimcodableCfg` can be degenerate.

**(e) Proof plan & estimated lines**
- `halting_re` (~5 lines, M6, Gemma T0): `Partrec.dom_re TM0Code.eval_partrec`.
- `halting_not_computable` (~55 lines, M6, Carbon): Apply `T-D(⇒)` to the universal `Nat.Partrec` map `e ↦ (Denumerable.ofNat Nat.Partrec.Code e).eval 0` (`PartrecCode.lean:1011`), then apply `TM0Code.exists_relabeling` (`T-C`) to get a single fixed `m₀ : TM0Code` and pointed injection `f : PointedMap Γ₀ ℕ` such that `(c.eval 0).Dom ↔ (StateTransition.eval (TM0.step m₀.machine) (TM0.init ((encNat (Encodable.encode c)).map f))).Dom`. Since `c ↦ (m₀, TM0.init ((encNat (Encodable.encode c)).map f))` is `Computable` (`primrec_encNat` + `Primrec.dom_finite f` + `tape_mk₁`), `ComputablePred` of `TM0Code` halting would contradict `ComputablePred.halting_problem 0` (`Halting.lean:64`).

---

#### `T-E(2)`: `TM0Code.exists_compiler`, `TM0Code.compile`, `TM0Code.primrec_compile`, `TM0Code.eval_compile_nat`, and `TM0Code.eval_compile`

**(a) Lean text (`spec/Spec.lean:532–568`)**
```lean
-- spec: T-E(2)
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
  sorry

-- spec: T-E(2)
noncomputable def TM0Code.compile : TM0Code → Nat.Partrec.Code :=
  TM0Code.exists_compiler.choose

-- spec: T-E(2)
theorem TM0Code.primrec_compile : Primrec TM0Code.compile := by
  sorry

-- spec: T-E(2)
theorem TM0Code.eval_compile_nat (m : TM0Code) (n : ℕ) :
    (TM0Code.compile m).eval n =
      (Part.ofOption (Encodable.decode (α := TM0.Cfg ℕ ℕ) n)).bind fun c ↦
        (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode := by
  sorry

-- spec: T-E(2)
theorem TM0Code.eval_compile (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    (TM0Code.compile m).eval (Encodable.encode c) =
      (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode := by
  sorry
```

**(b) Mathematical meaning**
Provides a uniform primitive-recursive (and hence computable) compiler `TM0Code.compile : TM0Code → Nat.Partrec.Code` translating any coded Turing machine `m` into an explicit Kleene recursive code `compile m` whose evaluation on any `n : ℕ` decodes `n` as `TM0.Cfg ℕ ℕ` (diverging cleanly when `decode n = none`) and runs `m.machine` (`eval_compile_nat`), and in particular on `Encodable.encode c` agrees identically with `(StateTransition.eval (TM0.step m.machine) c).map Encodable.encode` (`eval_compile`).

**(c) Mathlib source citations**
- `Nat.Partrec.Code`, `Nat.Partrec.Code.curry`, `Nat.Partrec.Code.eval`, `Nat.Partrec.Code.eval_curry`, `Nat.Partrec.Code.primrec₂_curry`, `Nat.Partrec.Code.exists_code` — `Mathlib/Computability/PartrecCode.lean:74, 111, 458, 501, 509, 530`
- `Part.ofOption` — `Mathlib/Data/Part.lean:216`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode*: Without `Primrec compile` (or `Computable compile`), `Classical.choice` on `T-A'` (`∀ m, ∃ c, ...`) would already yield an uncomputable map `TM0Code → Code` with zero uniformity content! Conversely, `Primrec compile` ensures `compile` is uniformly primitive recursive via Kleene's $S^m_n$ (`Code.curry`), `eval_compile_nat` pins divergence (`Part.none`) outside `Set.range Encodable.encode`, and `Encodable.encode` on `TM0.Cfg ℕ ℕ` is fixed by `instPrimcodableCfg`. (Note: `TM0Code.compile` is marked `noncomputable` in Lean's VM only because `exists_code` uses `Classical.choose` to pick the single constant universal code `c_univ`; mathematically `Primrec TM0Code.compile` holds unconditionally!)

**(e) Proof plan & estimated lines**
- (~40 lines, M6, Carbon/Gemma T1): From `TM0Code.eval_partrec` (`T-C`), define `u : ℕ →. ℕ := Nat.unpaired fun em ec ↦ (Part.ofOption (decode (α := TM0Code) em)).bind fun m ↦ (Part.ofOption (decode (α := TM0.Cfg ℕ ℕ) ec)).bind fun c ↦ (StateTransition.eval (TM0.step m.machine) c).map encode`. Prove `Nat.Partrec u` (`Partrec₂.unpaired'` + `Partrec.bind`), pick `c_univ` from `Code.exists_code.mp`, set `compile m := c_univ.curry (Encodable.encode m)`, prove `Primrec compile` via `Code.primrec₂_curry.comp (.const c_univ) Primrec.encode`, verify `eval_compile_nat` via `Code.eval_curry` + `Encodable.encodek`, and specialize at `n = Encodable.encode c` for `eval_compile`.

---

#### `T-E(3)`: `encUniv`, `decUniv`, `exists_universal_tm0`, `U`, `U_eval`, `U_evalCfg_tape`, and `U_mem_evalCfg_iff`

**(a) Lean text (`spec/Spec.lean:570–659`)**
```lean
-- spec: T-E(3)
def encUniv (mc : TM0Code × TM0.Cfg ℕ ℕ) : List Γ₀ :=
  encNat (Encodable.encode mc)

-- spec: T-E(3)
def decUniv (L : ListBlank Γ₀) : TM0.Cfg ℕ ℕ :=
  (Encodable.decode (decNat L)).getD default

-- spec: T-E(3)
theorem primrec_encUniv : Primrec encUniv := by sorry
theorem primrec_decUniv : Primrec decUniv := by sorry
theorem decUniv_encNat_encode (c : TM0.Cfg ℕ ℕ) :
    decUniv (ListBlank.mk (encNat (Encodable.encode c))) = c := by sorry

-- spec: T-E(3)
theorem exists_universal_tm0 :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (_ : Inhabited Λ)
      (U : TM0.Machine Γ₀ Λ),
      (∀ (m : TM0Code) (c : TM0.Cfg ℕ ℕ),
        (TM0.eval U (encUniv (m, c))).map decUniv =
          StateTransition.eval (TM0.step m.machine) c) ∧
      (∀ (m : TM0Code) (c : TM0.Cfg ℕ ℕ),
        (StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c)))).map TM0.Cfg.Tape =
          (StateTransition.eval (TM0.step m.machine) c).map
            fun c' ↦ Tape.mk₁ (encNat (Encodable.encode c'))) := by
  sorry

-- Named universal machine U, UniversalΛ, and plain instances (per Q4):
noncomputable def UniversalΛ : Type := exists_universal_tm0.choose
noncomputable instance instFintypeUniversalΛ : Fintype UniversalΛ := ...
noncomputable instance instDecidableEqUniversalΛ : DecidableEq UniversalΛ := ...
noncomputable instance instInhabitedUniversalΛ : Inhabited UniversalΛ := ...
noncomputable def U : TM0.Machine Γ₀ UniversalΛ := ...

-- spec: T-E(3)
theorem U_eval (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    (TM0.eval U (encUniv (m, c))).map decUniv =
      StateTransition.eval (TM0.step m.machine) c := by sorry

-- spec: T-E(3)
theorem U_evalCfg_tape (m : TM0Code) (c : TM0.Cfg ℕ ℕ) :
    (StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c)))).map TM0.Cfg.Tape =
      (StateTransition.eval (TM0.step m.machine) c).map
        fun c' ↦ Tape.mk₁ (encNat (Encodable.encode c')) := by sorry

-- spec: T-E(3)
theorem U_mem_evalCfg_iff (m : TM0Code) (c c' : TM0.Cfg ℕ ℕ) :
    c' ∈ StateTransition.eval (TM0.step m.machine) c ↔
      ∃ u' ∈ StateTransition.eval (TM0.step U) (TM0.init (encUniv (m, c))),
        u'.Tape = Tape.mk₁ (encNat (Encodable.encode c')) := by sorry
```

**(b) Mathematical meaning**
Constructs a **single fixed finite-state universal Post–Turing machine** `U : TM0.Machine Γ₀ UniversalΛ` over the 1250-symbol alphabet `Γ₀`, together with explicit primitive-recursive input/output maps `encUniv : TM0Code × TM0.Cfg ℕ ℕ → List Γ₀` and `decUniv : ListBlank Γ₀ → TM0.Cfg ℕ ℕ`. For every coded machine `m` and initial configuration `c`:
1. `(TM0.eval U (encUniv (m, c))).map decUniv` equals `StateTransition.eval (TM0.step m.machine) c`;
2. Even more strongly (`U_evalCfg_tape`), `U` started from `TM0.init (encUniv (m, c))` halts if and only if `m.machine` started from `c` halts, and when `m.machine` halts at `c'`, **the entire two-sided halting tape of `U` is literally `Tape.mk₁ (encNat (Encodable.encode c'))`** (head at `0`, `encNat (Encodable.encode c')` on cells `0 .. L - 1` with zero blanks by `default_notMem_encNat`, and `default` on all negative cells and all cells `≥ L`).

**(c) Mathlib source citations**
- `Turing.Tape.mk₁` — `Mathlib/Computability/TuringMachine/Tape.lean:493`
- `Turing.TM0.Machine`, `TM0.Cfg.Tape`, `TM0.step`, `TM0.init`, `TM0.eval` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:133, 146, 157, 167, 171`
- `StateTransition.eval` — `Mathlib/Computability/StateTransition.lean:33`
- `Turing.TM2to1.TrCfg` (`Tape.mk' ∅ (addBottom L)` full-tape invariant) — `Mathlib/Computability/TuringMachine/StackTuringMachine.lean:632–635`
- `Turing.TM1to0.trCfg`, `TM1to0.tr_respects` — `Mathlib/Computability/TuringMachine/PostTuringMachine.lean:520, 523`

**(d) How could this statement be wrong or vacuous?**
- *Failure mode 1 (existential `dec` Route-1 trap)*: If `dec` were existentially quantified (`∃ enc dec, Primrec enc ∧ Primrec dec ∧ ...`), a "universal" machine `U_fake` could simply count steps until `m` halts and leave `(m, c, N)` on its tape without actually computing `c'`, delegating `(TM0.step m.machine)^[N] c` to the primitive-recursive `dec`! Pinning `encUniv` and `decUniv` as **concrete named definitions** (`decUniv L = (decode (decNat L)).getD default`, which performs only binary-to-`ℕ` conversion and tuple unpairing) makes simulation-by-decoder impossible.
- *Failure mode 2 (input leakage into open target window — CMPP Anti-Vacuity Rule)*: In `S4TuringPoisson` (`MISSION_DIRECTIVE_CMPP.md` §4.4 & §5 I2), `encodeOpen (M, k, w)` must depend **only** on `(M, k, w)`, never on the input tape! Because `U_evalCfg_tape` guarantees `u'.Tape = Tape.mk₁ (encNat (Encodable.encode c'))`, CMPP B2+I2 can define the accepting open set for `(M, k, w)` as the union over *all* configurations `c'` matching `(k, w)` of the open Cantor cylinder corresponding to `Tape.mk₁ (encNat (Encodable.encode c'))` on `[-L(c'), L(c')]` (`L(c') = (encNat (Encodable.encode c')).length`). By `default_notMem_encNat`, cell `L(c')` is `default` on `c'` and non-`default` on any strict extension `encNat (Encodable.encode c'')`, so these cylinders isolate each `c'` cleanly with **zero dependence on the initial input tape**!
- *Failure mode 3 (divergence mismatch)*: As analyzed in §0.4, `U_evalCfg_tape` is stated as a `Part (Tape Γ₀)` equality, ruling out halting with garbage tapes on diverging inputs.

**(e) Proof plan & estimated lines**
- (~120–180 lines, M6, Carbon, reusing M5's `(⇒)` full-tape lemma!): Strengthen M5's internal `(⇒)` helper slightly so that for any `Nat.Partrec` function `g : ℕ →. ℕ`, the restricted finite-state `TM0` machine `M_g` built via `restrictSupportedTM0` satisfies `(StateTransition.eval (TM0.step M_g) (TM0.init (encNat n))).map TM0.Cfg.Tape = (g n).map (Tape.mk₁ ∘ encNat)` (this already holds from `TM2to1.TrCfg` at `StackTuringMachine.lean:635`, `TM1to0.tr_respects` at `PostTuringMachine.lean:523`, and `step_restrictSupportedTM0`!). Per user decision **Q4**, in M6 define `(UniversalΛ, U)` **directly** via `restrictSupportedTM0` applied to `g n := (Part.ofOption (decode (α := TM0Code × TM0.Cfg ℕ ℕ) n)).bind fun mc ↦ (StateTransition.eval (TM0.step mc.1.machine) mc.2).map encode` (with plain non-scoped `Fintype`/`DecidableEq`/`Inhabited` instances on `UniversalΛ`, avoiding `Exists.choose` on `Type`). Then `U_evalCfg_tape` is immediate at `n = encode (m, c)` (`encodek`); `U_eval` follows by `.map (decUniv ∘ Tape.right₀)` + `Tape.mk'_right₀` + `decUniv_encNat_encode`; `exists_universal_tm0` follows in 1 line as `⟨UniversalΛ, inferInstance, inferInstance, inferInstance, U, U_eval, U_evalCfg_tape⟩`; and `U_mem_evalCfg_iff` follows from `U_evalCfg_tape` + `Part.mem_map_iff` + injectivity of `Tape.mk₁ ∘ encNat ∘ encode`.

---

## 2. Faithfulness Checklist (`MISSION_DIRECTIVE.md` §2.1–2.10)

| # | Directive §2 Criterion | Pass? | Concrete Evidence in `spec/Spec.lean` & `docs/S1_statements.md` |
|---|---|---|---|
| **2.1** | **Faithfulness**: Headline statements use only Mathlib's `StateTransition.eval`, `TM0.step`, `TM0.eval`; raw list-based steppers are internal tools only. | **YES** | Verified across all headline declarations in `spec/Spec.lean`: `StateTransition.eval_partrec` (L26), `StateTransition.eval_partrec₂` (L33), `TM0.step_primrec_of_primrec` (L290), `TM0.step_primrec` (L299), `TM0.evalCfg_partrec` (L308), `TM0.eval_partrec` (L317), `TM0.exists_code_eval` (L327), `TM0Code.step_primrec` (L370), `TM0Code.eval_partrec` (L377), `TM0Code.exists_relabeling` (L386), `nat_partrec_iff_exists_tm0` (L508), `TM0Code.halting_re` / `halting_not_computable` (L519, L527), `TM0Code.exists_compiler` / `eval_compile_nat` / `eval_compile` (L536, L556, L563), `exists_universal_tm0` / `U_eval` / `U_evalCfg_tape` (L602, L638, L647). Zero custom steppers appear in `spec/Spec.lean`. |
| **2.2** | **Quotients**: `ListBlank` is a quotient; canonical form `trim` is the computational bridge; `Primrec` lemmas factor through `trim`. | **YES** | `ListBlank.trim` is given as a real `sorry`-free `ListBlank.liftOn (List.rdropWhile (· == default))` definition (`spec/Spec.lean:65–71`); `instPrimcodableListBlank` (L164–169) encodes `L` via `listBlankEquivCanonical` (`L ↦ ⟨L.trim, _⟩`), with `trim_mk` (L76), `mk_trim` (L82), `trim_injective` (L88), and `trim_congr` (L94). |
| **2.3** | **Instances**: `Primcodable` on `ListBlank`, `Tape`, `Cfg` (plus `Dir`, `TM0.Stmt`, `Γ₀`, and `Fintype K'`) are **scoped** in `namespace TuringRecursive` to prevent Mathlib diamonds; round-trip statements included. | **YES** | `instPrimcodableDir` (L124), `instDecidableEqStmt` (L140), `instPrimcodableStmt` (L145), `instPrimcodableListBlank` (L164 — taking **only** `[Inhabited Γ] [Primcodable Γ]`, zero `[DecidableEq Γ]` diamond!), `instPrimcodableTape` (L180), `instPrimcodableCfg` (L194), `instFintypeK'` (L421), `instDecidableEqΓ₀` (L451), and `instPrimcodableΓ₀` (L462) are all declared `scoped instance` inside `namespace TuringRecursive` (while project-owned `TM0Code` and `UniversalΛ` carry plain `instance`s, zero Mathlib diamond risk), with round-trip statements `decode_encode_*` (L261–283, L364, L466). |
| **2.4** | **Choice independence**: Statements quantify over arbitrary `[Primcodable Γ]` / `[Primcodable Λ]` on `[Finite Γ]` / `[Finite Λ]`; never bake `Fintype.equivFin` or `[DecidableEq]` into `T-A` / `T-A'`. | **YES** | `TM0.step_primrec` (L299), `TM0.evalCfg_partrec` (L308), `TM0.eval_partrec` (L317), and `TM0.exists_code_eval` (L327) assume `{Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ] [Finite Γ] [Finite Λ]` — neither `Fintype` nor `DecidableEq` nor `equivFin` appears. Likewise `TM0Code.exists_relabeling` (L386) assumes only `[Inhabited Γ] [Inhabited Λ] [Finite Γ] [Finite Λ]`. |
| **2.5** | **Uniformity**: Single type `TM0Code` over `ℕ`; out-of-range halts (`none`), so every code denotes a machine. | **YES** | `structure TM0Code` (L340) wraps `table : List (List (Option (ℕ × TM0.Stmt ℕ)))` and `TM0Code.machine` (L346) is `fun q a ↦ (m.table[q]?).bind fun row ↦ (row[a]?).join` — total on all `m : TM0Code`, halting out-of-bounds. |
| **2.6** | **Fixed encodings**: Every encoding in `T-D` and `T-E` is a concrete named function, never existentially quantified. | **YES** | `Γ₀` (L446), `encNat` (L472), `decNat` (L478), `encUniv` (L573), and `decUniv` (L579) are concrete, computable, `sorry`-free definitions. Neither `nat_partrec_iff_exists_tm0` (L508) nor `exists_universal_tm0` (L602) existentially quantifies over any encoding or decoding function. |
| **2.7** | **Universes**: `Type*` throughout, except `T-D` (and `T-E(3)`)'s existential state type `Λ : Type` forced by fixed `Γ₀ : Type`. | **YES** | `T-B` (`{α σ : Type*}`), `E` (`{α : Type*}`, `{Γ Λ : Type*}`), `T-A` / `T-A'` (`{Γ Λ : Type*}`), and `T-C` relabeling (`{Γ Λ : Type*}`) are fully universe-polymorphic. Only `nat_partrec_iff_exists_tm0` (L510) and `exists_universal_tm0` (L603) quantify `∃ (Λ : Type), ...` over fixed `Γ₀ : Type`. |
| **2.8** | **Output convention**: `TM0.eval` returns `Tape.right₀`, and `T-A` (as well as `T-C` and `T-E(3)`) also provides full-configuration `StateTransition.eval` versions. | **YES** | `T-A` provides both `TM0.evalCfg_partrec` (L308) and `TM0.eval_partrec` (L317); `T-C` `exists_relabeling` (L386) provides both `StateTransition.eval` and `TM0.eval` clauses; `T-E(3)` provides both `U_eval` (L638) and full-tape `U_evalCfg_tape` (L647). |
| **2.9** | **Upstreamability (Q2: Mathlib-PR quality)**: Mathlib naming/docstrings, ≤100 columns, generality (`T-B` and `step_primrec_of_primrec` stated without finiteness), generic list lemmas cleanly separable. | **YES** | Verified ≤100 columns on all 661 lines of `spec/Spec.lean`; docstrings on all structures/defs/headline theorems; `_root_.StateTransition.*`, `_root_.Primrec.list_rdropWhile`, `_root_.Primrec.list_dropLast`, `_root_.Primrec.listBlank_*`, `_root_.Primrec.tape_*`, `_root_.Turing.ListBlank.*`, and `_root_.Turing.TM0.*` use canonical Mathlib namespaces (`step_primrec_of_primrec` at L290 assumes only `Primrec₂ M`). |
| **2.10** | **Mathlib gaps S0 found accounted for**: `Primrec.list_rdropWhile`, `Primrec.list_dropLast`, `Fintype PartrecToTM2.K'`, `reaches_iff_exists_iterate` (plus critique of `Computable.iterate` / `Primrec.dite`). | **YES** | `StateTransition.reaches_iff_exists_iterate` (L40), `Primrec.list_rdropWhile` (L51), `Primrec.list_dropLast` (L57), and `instFintypeK'` (L421) are explicitly specified in `spec/Spec.lean` (plus `instDecidableEqStmt`, `instDecidableEqΓ₀`, `instPrimcodableΓ₀` discovered in S1). Per Q5, `Computable.iterate` and `Primrec.dite` are dropped as standalone deliverables because `Partrec.fix` handles `StateTransition.eval` directly. |

---

## 3. Gate S1 Decisions (Q1–Q5 — RESOLVED & FROZEN, 21 Nov 2026)

All five judgement calls from S1 review (`@spec` + `@verifier-tm`) have been approved by the user and applied in `spec/Spec.lean` (`b9ee4acddccaaadf68471374b570fd783e95dded44ac429183edc76e43afeb3a`):

1. **Q1 (`Function.Injective f ∧ Function.Injective g` in `TM0Code.exists_relabeling`, `T-C`) — KEPT (FROZEN)**:
   - Mandatory anti-vacuity condition preventing constant-zero collapse on total halting machines (§0.1) and enabling window symbol inversion `(c.map f g).Tape.nth i = f (w i) ↔ c.Tape.nth i = w i` in CMPP B2.

2. **Q2 (Namespace of `ListBlank` / `Tape` `Primrec` Lemmas, `E`) — MOVED TO `_root_.Primrec.*` (FROZEN)**:
   - Renamed `listBlank_mk`..`tape_right₀` to `_root_.Primrec.listBlank_mk`..`_root_.Primrec.tape_right₀` (`spec/Spec.lean:201–258`), matching Mathlib's `Primrec.list_*` / `Primrec.option_*` convention and enabling uniform dot-notation (`Primrec.tape_mk₂.comp ...`).

3. **Q3 (`TM0Code.eval_compile_nat` alongside `TM0Code.eval_compile`, `T-E(2)`) — BOTH INCLUDED (FROZEN)**:
   - Added the all-`n : ℕ` clause `(compile m).eval n = (Part.ofOption (Encodable.decode (α := TM0.Cfg ℕ ℕ) n)).bind fun c ↦ (StateTransition.eval (TM0.step m.machine) c).map Encodable.encode` to `TM0Code.exists_compiler` (`spec/Spec.lean:536`) and exposed `TM0Code.eval_compile_nat` (`L556`) alongside `TM0Code.eval_compile` (`L563`).

4. **Q4 (Direct `(UniversalΛ, U)` Definition in M6 + Plain Instances on `UniversalΛ`, `T-E(3)`) — APPROVED (FROZEN)**:
   - Changed `instFintypeUniversalΛ`, `instDecidableEqUniversalΛ`, and `instInhabitedUniversalΛ` (`spec/Spec.lean:620–629`) to plain (non-scoped) `instance`s on project-owned `UniversalΛ`, and recorded in §1.6 that Milestone M6 will define `(UniversalΛ, U)` directly via `restrictSupportedTM0` (proving `exists_universal_tm0` in 1 line from `(UniversalΛ, U, U_eval, U_evalCfg_tape)` without `Exists.choose` on `Type`).

5. **Q5 (`Computable.iterate` and `Primrec.dite` in §2.10) — DROPPED AS STANDALONE DELIVERABLES (FROZEN)**:
   - Dropped as standalone milestone gates since `Partrec.fix` (`Partrec.lean:769`) proves `StateTransition.eval_partrec` directly; M1–M6 may still add either as an internal helper if useful.
