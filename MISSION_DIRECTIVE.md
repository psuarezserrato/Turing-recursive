# MISSION DIRECTIVE (TM→Partrec): Turing machines are computed by partial recursive functions

**Purpose.** Formalize, carefully and independently, that the evaluation of a Turing machine is a partial recursive function
(the "machines ⇒ recursive functions" half of the Church–Turing equivalence), uniformly in the machine. This is foundational,
and it is the prerequisite for Track B (B2, universal machine) of `MISSION_DIRECTIVE_CMPP.md`, which is **blocked until this mission lands**.

Toolchain: Lean `v4.36.0`, Mathlib pinned to the **same commit** as S4TuringPoisson
(`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, from `S4TuringPoisson/lake-manifest.json`), so the result can later be `require`d by S4TP and TauCeti-based projects without conflicts.
Standing rules from `.agents/rules/lean-integrity.md` apply (zero `sorry`/`axiom`, junk-value vigilance, isolated worktrees, 24 GB RAM guardrails, 5-retry escalation).

---

## 0. The gap (verified against the pinned Mathlib, 21 Nov 2026)

| Mathlib / TauCeti file | What it gives | What it does not give |
|---|---|---|
| `Computability/TuringMachine/ToPartrec.lean`, `Config.lean` | **Partrec ⇒ TM**: a `TM2` machine evaluating `ToPartrec.Code` (`PartrecToTM2.tr_eval`) | the converse |
| `Computability/TuringMachine/Computable.lean` | `TM2Computable`, `TM2ComputableInPolyTime` (complexity-oriented definitions) | any link to `Partrec` |
| `PostTuringMachine.lean`, `StackTuringMachine.lean`, `Tape.lean` | TM0/TM1/TM2 semantics, translations `TM1to0.tr_eval`, `TM2to1.tr_eval`, `TM0.Machine.map`, `Machine.map_step`, `Machine.map_respects` | `Primcodable` instances for `ListBlank`, `Tape`, `Cfg`; any `Primrec`/`Partrec` statement |
| `StateTransition.lean` (namespace `StateTransition`) | `eval` (a `PFun.fix`), `mem_eval`, `Reaches`, `reaches_eval`, `tr_eval'`, `EvalsTo` | partrec-ness of `StateTransition.eval` (easy, see T-B) |
| `PartrecCode.lean`, `Halting.lean`, `Partrec.lean`, `Primrec/*` | `Code.eval`, `exists_code`, `curry`/`eval_curry`, `halting_problem`, `Partrec.rfind`, `Primrec.nat_iterate`, `Primrec.dom_finite`, `Primcodable.ofEquiv`, `Primcodable.subtype`, list primrec lemmas | — (these are our tools) |
| TauCeti `Computability/*` | degrees, priority methods, primrec lists | nothing on Turing machines |

S4TP already has a related but **non-general** result: `universalHaltingTM0` (M3.2) translates one fixed Mathlib Partrec program into a TM0 (the *easy* direction), and `FinTM0.reaches_iff_exists_iterate_stepOpt` (a reusable lemma).

---

## 1. Headline results (CORRECTED after S0; final names/typeclasses frozen at gate S1)

All statements are about Mathlib's own `StateTransition.eval`, `Turing.TM0.step`, `Turing.TM0.eval`
(**`Turing.eval` does not exist**: the generic evaluator lives in namespace `StateTransition`, verified in `StateTransition.lean:28,33`).
Everything is universe-polymorphic (`Type*`) except where a *fixed* type forces `Type`; `Primcodable`, `Primrec`, `Partrec`, `Computable` all accept `Type*` (verified).

| ID | Statement (sketch) | Role / S0 proof plan |
|---|---|---|
| **T-B (generic)** | `StateTransition.eval_partrec {σ : Type*} [Primcodable σ] {f : σ → Option σ} (hf : Computable f) : Partrec (StateTransition.eval f)`; parametrized `eval_partrec₂ (hf : Computable₂ f) : Partrec₂ fun a => StateTransition.eval (f a)`; `reaches_iff_exists_iterate : Reaches f a b ↔ ∃ n, (flip Option.bind f)^[n] (some a) = some b` | **Easy**: `StateTransition.eval f` is *definitionally* a `PFun.fix`, so this is `Partrec.fix` (`Partrec.lean:769`) + `Computable.option_casesOn`. About 60-120 lines |
| **E (encodings)** | `List.rdropWhile` already exists in Mathlib. New generic lemmas `Primrec.list_rdropWhile`, `Primrec.list_dropLast` (1-liners). `ListBlank.trim [Inhabited Γ] [DecidableEq Γ] : ListBlank Γ → List Γ` with `trim_mk`, `mk_trim`, `trim_injective`; **scoped** `Primcodable (ListBlank Γ)` needing only `[Inhabited Γ] [Primcodable Γ]` (via `Encodable.decidableEqOfEncodable`, canonical subtype `{l // l.rdropWhile (· == default) = l}`, `Primcodable.ofEquiv`); `Primcodable Dir`, `TM0.Stmt Γ`, `Tape Γ`, `TM0.Cfg Γ Λ`; `Primrec` of `ListBlank.mk/trim/head/tail/cons/nth`, `Tape.move/write/mk₁/mk₂/nth/right₀`; round trip `decode (encode x) = some x` | Largest milestone: about 500-800 lines (S0). First targets are T0/T1 (gemma-first) |
| **T-A (fixed machine)** | General: `TM0.step_primrec_of_primrec (hM : Primrec₂ M) : Primrec (TM0.step M)` (any machine, no finiteness). Finite corollary under `[Inhabited Γ] [Inhabited Λ] [Primcodable Γ] [Primcodable Λ] [Finite Γ] [Finite Λ]` (**no `DecidableEq`**, via `Primrec.dom_finite`): `TM0.step_primrec`, `TM0.evalCfg_partrec : Partrec (StateTransition.eval (TM0.step M))`, **`TM0.eval_partrec : Partrec (TM0.eval M)`** | About 150-250 lines after E |
| **T-A′ (Nat level)** | `∃ c : Nat.Partrec.Code, ∀ l, c.eval (encode l) = (TM0.eval M l).map encode` (the literal Kleene form; uses `Primcodable (ListBlank Γ)` from E) | `exists_code` + `encodek` |
| **T-C (uniform)** | `structure TM0Code` (table `List (List (Option (ℕ × TM0.Stmt ℕ)))`, out-of-range gives halt, blank/start `0`), `Primcodable` via `ofEquiv`, `TM0Code.machine`; `Primrec₂ step`; **`TM0Code.eval_partrec : Partrec₂ fun m c => StateTransition.eval (TM0.step m.machine) c`**. Relabeling: for finite `M` there are `f : PointedMap Γ ℕ`, **`g : PointedMap Λ ℕ`** (pointed, so `TM0.map_init` applies) and a code `m` with `StateTransition.eval (TM0.step m.machine) (c.map f g) = (StateTransition.eval (TM0.step M) c).map (Cfg.map f g)` and `TM0.eval m.machine (l.map f) = (TM0.eval M l).map (ListBlank.map f)` | S0 note: `m.machine ≠ M.map …` globally (out-of-range halts vs wraps) but they agree on every reachable `(g q, f a)`, which is all `map_step` needs. About 250-450 lines |
| **T-D (equivalence)** | Fix alphabet `Γ₀ := TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')` (needs a `Fintype K'`; Mathlib has none, so provide it via an `Equiv` with `Fin 4`) and the **named** `encNat n := TM2to1.trInit K'.main (trList [n])`. `Nat.Partrec f ↔ ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (_ : Inhabited Λ) (M : TM0.Machine Γ₀ Λ), ∀ n, TM0.eval M (encNat n) = (f n).map (ListBlank.mk ∘ encNat)` | (⇒) uses `PartrecToTM2.tr_eval`, `tr_respects`, `TM1to0.tr_eval` and the finite-support restriction (S4TP `restrictSupportedTM0`); **do not use `TM2to1.tr_eval`** (it forgets that the other stacks are empty), apply `StateTransition.tr_eval` to `tr_respects`. (⇐) via T-A and an explicit primrec `decNat`. About 350-600 lines |
| **T-E (consequences)** | (1) TM0 halting is `REPred` and `¬ ComputablePred` over `TM0Code × Cfg ℕ ℕ`; (2) computable compiler `TM0Code → Nat.Partrec.Code` (`Code.curry`, `eval_curry`, `primrec₂_curry`); (3) **universal TM0** `U` over `Γ₀` with the **named** `encUniv (m,c) := encNat (encode (m,c))` and `decUniv`, *not existentially quantified* (an existential `dec` could trivialize the statement by re-running the machine), and the **windowed variant stated as exact output**: the halting tape of `U` is `Tape.mk₁ (encNat (encode c'))` (blank-free), so a cylinder of length `L = |encNat (encode c')|` isolates `c'` | About 300-550 lines. The window statement is what CMPP B2 (with refactor I2) consumes |
| **T-F (stretch, deferred)** | `TM1.eval`/`TM2.eval` partrec for finite-support machines | Q4: deferred |

Anti-vacuity witnesses are required for every item (§6 G5).

---

## 2. Design decisions and points requiring care (updated after S0)

1. **Faithfulness.** Headline statements use only Mathlib's `StateTransition.eval`, `TM0.step`, `TM0.eval`. Raw list-based steppers are internal tools only, with a proved simulation lemma.
2. **Quotients.** `ListBlank` is a quotient; the canonical form `trim` is the only way to compute on it. Every `Primrec` lemma factors through `trim`.
3. **Instances.** `Primcodable (ListBlank Γ)`, `Tape`, `Cfg` are **scoped** (namespace `TuringRecursive`) to avoid diamonds if Mathlib later adds its own; round-trip tests required. S0 confirmed Mathlib and TauCeti have **no** `Encodable/Primcodable/DecidableEq/Fintype` instance on `ListBlank`, `Tape`, `TM0.Cfg/Stmt/Machine`.
4. **Choice independence.** Statements quantify over arbitrary `[Primcodable Γ]`/`[Primcodable Λ]` on finite types (every function on a finite domain is primrec). Never bake `Fintype.equivFin` into a statement.
5. **Uniformity.** One type `TM0Code` over `ℕ`; out-of-range halts, so every code denotes a machine.
6. **Fixed encodings.** Every encoding in T-D/T-E is a concrete named function, never existentially quantified.
7. **Universes.** (Corrected.) `Type*` throughout. Only T-D's existential state type is `Type`, because the alphabet `Γ₀` is fixed.
8. **Output convention.** `TM0.eval` returns only `Tape.right₀`; T-A also provides the full-configuration version.
9. **Upstreamability (Q2: Mathlib-PR quality).** Mathlib naming/docstrings, `#lint`, at most 100 columns, generality (T-B and the general `step_primrec_of_primrec` are stated for arbitrary machines), no project-specific dependencies. Generic list/Primrec lemmas go in a separate small file so they can be PR'd independently.
10. **Mathlib gaps S0 found (small, to prove ourselves):** `Primrec.list_rdropWhile`, `Primrec.list_dropLast`, `Computable.iterate`, `Primrec.dite`, `Fintype PartrecToTM2.K'`, `reaches_iff_exists_iterate`.

---

## 3. Project setup

- New independent Lake project (decision Q1): `/Users/pablosuarez/Desktop/Turing-recursive`, library `TuringRecursive`, depends only on Mathlib at the pinned commit, toolchain `leanprover/lean4:v4.36.0`; `lake exe cache get` reuses the Mathlib cache already on disk. Own git repo, `main` + `.worktrees/<worker>`.
- Copy and adapt from S4TP: `tools/workflow_control.py`, `tools/bootstrap_worktree.sh`, `tools/ollama_lean4_client.py`, `config/ollama_gemma_config.json`, `.agents/rules/lean-integrity.md`, `.mcp.json`.
- Later (not in this mission's scope): S4TP adds `[[require]] name = "TuringRecursive", path = "../Turing-recursive"` and proves the `FinTM0`/`HaltsWithWindow` corollaries there.

---

## 4. Milestones

```mermaid
flowchart LR
  W0["W0 gemma engine + calibration"] --> S1
  S0["S0 explore (read-only)"] --> S1["S1 statements frozen<br/>user review"]
  S1 --> M1["M1 T-B generic eval"]
  S1 --> M2["M2 E encodings"]
  M1 --> M3["M3 T-A, T-A′"]
  M2 --> M3
  M3 --> M4["M4 T-C uniform + relabel"]
  M4 --> M5["M5 T-D equivalence"]
  M5 --> M6["M6 T-E consequences, universal TM0"]
  M6 --> M7["M7 T-F stretch"]
```

| ID | Owner | Deliverable | Done when | Est. lines |
|---|---|---|---|---|
| **W0** | `@gemma-infra` (Argon) | Local-model engine of `MISSION_DIRECTIVE_CMPP.md` §6.3–6.7, built **here first** and reused by CMPP: `gemma_loop.py` (compiler-in-the-loop, ≤5 attempts, escalation files), `index.py` (BM25 over pinned Mathlib incl. `Computability/*`), outcome ledger, provenance checker; calibration on ≥40 hidden Mathlib `Primrec`/`Partrec` lemmas (pass@1/pass@5 per tier) | `docs/gemma_calibration.md`, `docs/routing.md` | tooling only |
| **S0** | `@explorer` (read-only, Carbon) | Inventory: exact signatures of all lemmas in §0; check whether `Primrec` of list operations needed (`dropLast`, `reverse`, `getD`, `head?`, trailing-blank stripping) exist; how M3.2 handled finite supports in the Mathlib pipeline; plan for T-D encodings | board report | — |
| **S1** | `@spec` (Carbon) | All headline statements of §1 (corrected) and the M2 lemma list written as Lean declarations with `sorry` **on a spec branch only** (never merged), compiled; `docs/S1_statements.md` with a rationale and a Mathlib-source citation per statement | **user reviews and approves the statements**; verifier signs the faithfulness checklist (§2.1–2.10) | 300–500 |
| **M1** | `@eval` | T-B, `Reaches ↔ ∃ n, iterate` (port of `FinTM0.reaches_iff_exists_iterate_stepOpt`) | 0 `sorry`, gates | 200–400 |
| **M2** | `@encode` | E: `trim`, scoped instances, primrec of tape/list-blank operations, round-trip tests; optional `primrec_tac` macro (a `first` over `Primrec.comp/pair/fst/snd/option_casesOn/list_*` combinators) to help both gemma and frontier | gates | 800–1500 |
| **M3** | `@eval` | T-A, T-A′ | gates | 300–600 |
| **M4** | `@uniform` | T-C, relabeling theorem | gates | 800–1500 |
| **M5** | `@church-turing` | T-D (finite-support restriction of the translated machine; reuse the idea of S4TP `restrictSupportedTM0`) | gates | 600–1200 |
| **M6** | `@church-turing` | T-E (1)–(3), windowed universal TM0 | gates | 400–800 |
| **M7** | `@uniform` | T-F (stretch, may be deferred) | gates | 500–1000 |

Total estimate after S0: **about 2.5-5k lines** (S0 sums to roughly 2.0-4.3k; kept conservative). The mathematics is classical and shorter than first feared (T-B is nearly definitional). The risk is engineering: quotient encodings (M2) and the finite-support restriction (M5). These are S0 estimates, not yet validated by proofs.

---

## 5. Local-model-first (D4 carried over)

This library is the best place to make `gemma4:12B` carry real load: most declarations are **T0/T1 `Primrec` plumbing** (composition of known primrec maps, case analysis on `Option`/`Stmt`/`Dir`, list identities).
- Workflow per milestone: `@spec` (or the milestone owner) writes the declaration skeleton with `sorry`s → the gemma daemon attempts every `sorry` in the background (≤5 attempts each, compiler feedback, retrieval from Mathlib's `Primrec/*`) → frontier works **only** on escalation files.
- Expected local share (to be confirmed by W0 calibration): high for M2/M4 plumbing, low for M1's `Nat.rfind` argument and M5's support restriction.
- Concurrency: daemon + **one** frontier Lean worker (24 GB rule; the daemon's Lean checks occupy the second slot).
- Provenance gate G8 (CMPP §6.7) applies; milestone reports state counts by origin and per-tier acceptance rates.

---

## 6. Gates (a milestone merges only when all apply and pass)

- **G1** `LEAN_NUM_THREADS=2 lake build --wfail`; ≤100 columns; Mathlib `#lint` clean on new declarations.
- **G2** `collectAxioms` over every declaration ⊆ `{propext, Classical.choice, Quot.sound}`; comment-stripped scan finds no `sorry|admit|axiom|unsafe|implemented_by|native_decide|opaque|maxHeartbeats`.
- **G3** Statement freeze: headline statements identical to the S1-approved versions (`git diff` reviewed).
- **G4** Wiring: `#audit_wiring` (port from `SympTopAutoForm/tests/PhaseAxiomCensus.lean`) shows T-A depends on T-B and the M2 instances; T-D(⇐) depends on T-A.
- **G5** Anti-vacuity and sanity (verifier writes these, and must attempt refutations):
  - concrete machines: a halting machine (e.g. binary increment) and a looping machine; `TM0.eval` values checked by `decide`/`rfl` where feasible, and `Dom` true/false respectively;
  - encoding round trips and `trim` canonicity on explicit lists with trailing blanks;
  - **round-trip consistency with Mathlib**: for a concrete `ToPartrec.Code`, the TM from `PartrecToTM2` evaluated through T-A agrees with `Code.eval` (cross-checks our direction against Mathlib's);
  - T-E(1): TM0 halting is `¬ ComputablePred` (non-trivial consequence; impossible if the encodings were degenerate).
- **G6** Faithfulness checklist §2.1–2.8 signed by `@verifier-comp`.
- **G7** Honest labels: every deliverable UNCONDITIONAL (no class hypotheses in this mission).
- **G8** Local-model provenance and outcome ledger.

---

## 7. Risks

| Risk | Mitigation |
|---|---|
| `ListBlank` quotient makes primrec proofs painful | Canonical `trim` + subtype instance; all lemmas through `trim`; budgeted as the largest milestone (M2) |
| Missing list primrec lemmas (e.g. trailing-blank stripping) | S0 inventory; prove generic list lemmas first (gemma-first) |
| Dependent types in uniform codes | `TM0Code` over `ℕ` (§2.5) |
| M5 finite-support restriction of translated machines | Reuse the approach of S4TP `restrictSupportedTM0`; T-D may land after T-A/T-C without blocking M6(1)–(2) |
| Trivializing statements | S1 user review, fixed encodings, G5 refutation attempts |
| Mathlib bump changes names | Pinned commit; no bump during the mission |
| 12B model weak | Calibrate first; failure only costs background time |

Kill criterion: a milestone exceeding 3× its estimate with no green gate pauses the swarm and returns to the user.

---

## 8. Decisions (RESOLVED by the user, 21 Nov 2026)

| ID | Decision |
|---|---|
| **Q1** | Independent repo at `/Users/pablosuarez/Desktop/Turing-recursive` (Lake package `TuringRecursive`, Mathlib pinned to `fc4f59e5...`). Created and building (baseline commit `34c61b6`) |
| **Q2** | **Mathlib-PR quality**: Mathlib naming/style, docstrings, `#lint`, <=100 columns, generality, no project-specific dependencies |
| **Q3** | **(a)**: the encoding induced by Mathlib's `PartrecToTM2` through `TM2to1`/`TM1to0` (named, fixed, never existential) |
| **Q4** | **Defer** T-F (TM1/TM2) |

## 9. Interface delivered to `MISSION_DIRECTIVE_CMPP.md`

CMPP B2 consumes: T-C (`TM0Code.eval_partrec`, relabeling), T-E(2) (computable translation to `Nat.Partrec.Code`), and T-E(3) (windowed universal TM0). S4TP then proves, in its own repo, the `FinTM0`/`HaltsWithWindow` versions by relabeling and the `Tape.nth` window readout. B1 (Bennett) and B3 are unaffected and remain in CMPP.

## 10. Immediate next action
On approval of Q1–Q4: create the project (§3), run **W0** and **S0** in parallel (no frontier Lean worker), then **S1** and stop for the user's statement review.
