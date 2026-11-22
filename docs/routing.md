# Local-Model vs. Frontier Routing Policy (`Turing-recursive` TM $\to$ Partrec)

## 1. Empirical Routing Rule & W0 Calibration Decisions

Per `MISSION_DIRECTIVE.md` §5 and the W0 calibration protocol (`docs/gemma_calibration.md`), each declaration tier is assigned a routing policy strictly from its measured 40-lemma Mathlib `Computability/*` calibration `pass@5` rate:

- **`gemma-first`**: $\text{pass@5} \ge 30\%$ — run `tools/gemma_loop.py` (`--max-attempts 5`, `"keep_alive": 0`, `num_ctx=4096`, `MAX_PROMPT_CHARS=4000`, `think=false`) first; escalate to frontier (Carbon) only after 5 logged compiler-verified failures in `.agents/gemma_escalations/<decl>.json`.
- **`gemma-draft-only`**: $10\% \le \text{pass@5} < 30\%$ — optional 1–2 attempt local draft; frontier completes proof.
- **`frontier`**: $\text{pass@5} < 10\%$ — route directly to frontier (Carbon); do **not** burn 5 local attempts per declaration when empirical success is $< 10\%$.

| Tier | Scope / Declaration Profile | Measured **pass@1** | Measured **pass@5** | Mean Wall Time / Decl | Mean Tokens / Decl | Assigned Routing Policy |
|---|---|---:|---:|---:|---:|---|
| **T0** | Algebra, combinatorics, boilerplate: ` @[simp]` / `@[ext]` projections, `decode (encode x) = some x` round-trip wrappers, basic `List`/`ListBlank`/`Tape` `mk`/`move`/`write` definitional identities, `Equiv` component projections | **26.7% (4/15)** | **33.3% (5/15)** | **67.5 s** | **458.7** | **`gemma-first`** ($\ge 30\%$) |
| **T1** | Structured `Primrec`/`Computable` compositions, `Primrec.of_eq` pointwise reductions, `List`/`Option`/`Dir`/`TM0.Stmt` recursion and case analysis | **0.0% (0/15)** | **0.0% (0/15)** | **171.0 s** | **1,010.3** | **`frontier`** ($< 10\%$) |
| **T2** | Core `Partrec.fix` / `Nat.rfind` / `Primrec.nat_iterate` arguments, quotient well-definedness & injectivity (`ListBlank.trim_injective`), `TM0Code` relabeling & `Machine.map_step` simulation, finite-support restriction (`restrictSupportedTM0`), universal `TM0` & halting undecidability | **0.0% (0/10)** | **0.0% (0/10)** | **298.3 s** | **1,925.8** | **`frontier`** ($< 10\%$) |

---

## 2. Milestone-by-Milestone Routing Table (`M1`–`M7`)

Based on the frozen Gate S1 specification (`spec/Spec.lean`, 56 theorems + 18 definitions + 13 instances), the table below classifies every `TuringRecursive/` milestone file (`M1`–`M7`) by its declaration breakdown across T0, T1, and T2, the resulting expected share of declarations per tier, and the operational routing mode:

| Milestone | Target File (`TuringRecursive/`) | Headline Deliverables | Est. Total Decls | **T0 Share (`gemma-first`)** | **T1 Share (`frontier` + `primrec_tac`)** | **T2 Share (`frontier`)** | Operational Routing & Execution Guidance |
|---|---|---|---:|---:|---:|---:|---|
| **M1** | `TuringRecursive/Eval.lean` | **T-B**: `StateTransition.eval_partrec`, `eval_partrec₂`, `reaches_iff_exists_iterate` | ~8–12 | **~20%** (2–3 simple `iterate`/`Option.bind` base `@[simp]` lemmas) | **~30%** (2–4 step-function `Primrec`/`Computable` adapters for `PFun.fix`) | **~50%** (4–5 core `Partrec.fix` / `reaches_iff_exists_iterate` induction proofs) | **Frontier-led (T2/T1)**; run `gemma_loop.py --tier T0` on `-- tier: T0` `@[simp]` helpers only. |
| **M2** | `TuringRecursive/ListPrimrec.lean`, `TuringRecursive/Encoding.lean` | **E**: `Primrec.list_rdropWhile`, `list_dropLast`, `ListBlank.trim` (`trim_mk`, `mk_trim`, `trim_injective`, `trim_congr`), scoped `Primcodable` (`Dir`, `Stmt`, `ListBlank`, `Tape`, `Cfg`), `decode_encode_*` round-trips, `_root_.Primrec.listBlank_*` & `tape_*` | ~30–45 | **~35%** (10–15 `decode_encode_*` round-trips, `Equiv` projection `@[simp]` lemmas, `rdropWhile` base/nil lemmas) | **~45%** (14–20 `_root_.Primrec.listBlank_*`, `tape_*`, `list_dropLast`, `list_rdropWhile` compositions) | **~20%** (6–10 `ListBlank` quotient `liftOn` well-definedness, `trim_injective`, `listBlankEquivCanonical` proofs) | **Hybrid**: T0 round-trip & `@[simp]` wrappers go **`gemma-first`**; T1 `Primrec` lemmas & T2 quotient proofs go directly to **`frontier`** (using `tools/primrec_tac.lean` combinators where applicable). |
| **M3** | `TuringRecursive/TM0Eval.lean` | **T-A & T-A′**: `TM0.step_primrec_of_primrec`, `TM0.step_primrec`, `TM0.evalCfg_partrec`, `TM0.eval_partrec`, `TM0.exists_code_eval` | ~8–12 | **~20%** (2–3 projection/unfolding helpers) | **~40%** (3–5 `step_primrec_of_primrec` & `step_primrec` via `Primrec.dom_finite` + `option_map`) | **~40%** (3–4 `evalCfg_partrec`, `eval_partrec`, and `Nat.Partrec.Code.exists_code` bridge) | **Frontier-led (T1/T2)**; T0 unfolding helpers via **`gemma-first`**. |
| **M4** | `TuringRecursive/Uniform.lean` | **T-C**: `TM0Code`, `TM0Code.machine`, `instPrimcodableTM0Code`, `decode_encode_tm0Code`, `TM0Code.step_primrec`, `TM0Code.eval_partrec`, `TM0Code.exists_relabeling` (with `Injective f ∧ Injective g`) | ~18–28 | **~30%** (5–8 `TM0Code` projection `@[simp]` lemmas, `decode_encode_tm0Code`, out-of-bounds `none` simp lemmas) | **~35%** (6–10 `TM0Code.step_primrec` 2D table lookup `list_getElem?` / `option_bind` compositions) | **~35%** (6–10 `exists_relabeling` injective `PointedMap` construction + `Machine.map_step` / `tr_eval'` simulation) | **Hybrid**: T0 table/encoding `@[simp]` lemmas via **`gemma-first`**; T1 `step_primrec` and T2 relabeling simulation via **`frontier`**. |
| **M5** | `TuringRecursive/Equivalence.lean` | **T-D**: `Γ₀`, `instFintypeK'`, `instDecidableEqΓ₀`, `instPrimcodableΓ₀`, `encNat`, `decNat`, `primrec_encNat`, `primrec_decNat`, `default_notMem_encNat`, `nat_partrec_iff_exists_tm0` | ~25–35 | **~25%** (6–9 `Γ₀`/`K'` equivalence `@[simp]` lemmas, `decode_encode_Γ₀`, `encNat`/`decNat` small base lemmas) | **~30%** (7–10 `primrec_encNat`, `primrec_decNat`, binary-digit list `foldl`/`unfold` lemmas) | **~45%** (11–16 `PartrecToTM2` $\to$ `TM2to1` $\to$ `TM1to0` finite-support state restriction `restrictSupportedTM0` & simulation) | **Frontier-led (T2-dominant)**; T0 `Γ₀`/`K'` boilerplate via **`gemma-first`**. |
| **M6** | `TuringRecursive/Universal.lean` | **T-E(1)–(3)**: `TM0Code.halting_re`, `TM0Code.halting_not_computable`, `TM0Code.compile` (`eval_compile_nat`, `eval_compile`), `encUniv`, `decUniv`, `(UniversalΛ, U)`, `U_eval`, `U_evalCfg_tape` | ~15–22 | **~20%** (3–5 `encUniv`/`decUniv` round-trip & `@[simp]` helpers) | **~25%** (4–6 `primrec_encUniv`, `primrec_decUniv`, `Code.curry` wrapper lemmas) | **~55%** (8–12 halting problem reduction, `compile` specification, universal `TM0` exact halting-tape theorem `U_evalCfg_tape`) | **Frontier-led (T2-dominant)**; T0 `encUniv`/`decUniv` round-trip helpers via **`gemma-first`**. |
| **M7** | `TuringRecursive/Stretch.lean` | **T-F (Deferred per Q4)**: `TM1.eval` / `TM2.eval` partrec for finitely supported machines | Deferred | ~25% | ~35% | ~40% | **Deferred per user decision Q4** (`MISSION_DIRECTIVE.md` §8). |

---

## 3. Hardware & Provenance Rules for Active Milestones

1. **Mandatory 24 GB Unified RAM Settings (`config/ollama_gemma_config.json`)**:
   - `primary_model`: `"gemma4:12B"`
   - `locked_num_ctx`: `4096`
   - `max_prompt_chars`: `4000` (`top_k=4` premises, `top_k=1` accepted proof, $\le 12$ compiler error lines)
   - `keep_alive`: `0` (numeric `0` — forces immediate MLX runner unload after each call so Ollama and `lake env lean` never coexist in unified RAM, holding inference memory at **7.7 GB** and swap $\le 3.8\text{ GB}$)
   - `think`: `false` across all attempts (`num_predict = 384` for attempts 1–3, `512` for attempts 4–5)
   - `LEAN_NUM_THREADS=2` and at most **1–2 concurrent Lean processes** across the entire machine.
2. **Gate G8 Provenance Enforcement (`tools/check_gemma_provenance.py`)**:
   - Every new declaration explicitly tagged `-- tier: T0` (i.e. in the **`gemma-first`** tier) MUST have either a verified accepted proof in `.agents/gemma_accepted/<decl>.lean` or an escalation record in `.agents/gemma_escalations/<decl>.json` with 5 logged failed attempts.
   - Because **T1** measured **`0.0%` (`0/15`)** in W0 calibration and is classified as **`frontier`** ($\text{pass@5} < 10\%$), `tools/check_gemma_provenance.py` defaults to `--tiers T0`, enforcing Gemma provenance on all `gemma-first` (`T0`) declarations while routing `T1`/`T2` directly to `frontier`.
