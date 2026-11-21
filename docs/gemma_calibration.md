# W0 Local-Model Calibration Report (`gemma4:12B` on Pinned Mathlib `fc4f59e5`)

## 1. Executive Summary

We evaluated the local `gemma4:12B` model (4-bit `nvfp4` via Ollama `0.40.16` MLX runner on 24 GB unified Apple Silicon RAM) using the compiler-in-the-loop prover (`tools/gemma_loop.py`), pure-Python BM25 premise/proof retriever (`tools/index.py`, indexing 19,746 declarations and 3,260 accepted proofs), and verified outcome ledger (`tools/ledger.py`) across **40 stratified, already-proved lemmas** from pinned Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, Lean `v4.36.0`) in `Mathlib/Computability/{Primrec/*,Partrec,PartrecCode,StateTransition,TuringMachine/*}`.

| Tier | Description | Lemmas ($N$) | Verified Attempts | **pass@1** | **pass@5** | Mean Wall Time / Decl | Mean Model Latency / Attempt | Mean Lean Check / Attempt | Mean Tokens / Attempt | Mean Tokens / Decl | Routing Rule Outcome |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| **T0** | Algebra / combinatorics / boilerplate (`BlankExtends`, `BlankRel`, `ListBlank`, `Tape` move/mk'/write/map, `simp`/`ext`) | 15 | 56 | **4 / 15 (26.7%)** | **5 / 15 (33.3%)** | 67.5 s | 13,791.8 ms (13.8 s) | 4,217.4 ms (4.2 s) | 122.9 | 458.7 | **`gemma-first`** ($\text{pass@5} \ge 30\%$) |
| **T1** | Structured (`Primrec` composition, `Option`/`List` combinators, list induction, `Tape`/`Dir` case analysis) | 15 | 75 | **0 / 15 (0.0%)** | **0 / 15 (0.0%)** | 171.0 s | 29,078.7 ms (29.1 s) | 5,061.2 ms (5.1 s) | 202.1 | 1,010.3 | **`frontier`** ($\text{pass@5} < 10\%$) |
| **T2** | Core (`Primrec.nat_iterate`, `Primrec.dom_finite`, `Partrec.rfindOpt`, `Code` bounds, `StateTransition` & `TM0.Machine.map_step` simulation) | 10 | 50 | **0 / 10 (0.0%)** | **0 / 10 (0.0%)** | 298.3 s | 53,306.3 ms (53.3 s) | 6,273.5 ms (6.3 s) | 385.2 | 1,925.8 | **`frontier`** ($\text{pass@5} < 10\%$) |
| **All** | **Full Stratified 40-Lemma Benchmark** | **40** | **181** | **4 / 40 (10.0%)** | **5 / 40 (12.5%)** | **164.0 s** | **31,040.3 ms (31.0 s)** | **5,135.1 ms (5.1 s)** | **228.1** | **1,032.3** | **T0 `gemma-first`; T1/T2 `frontier`** |

### Plain Assessment

1. **Tier T0 (`pass@1 = 26.7%`, `pass@5 = 33.3%`, mean `67.5 s/decl`)**: `gemma4:12B` reliably closes short 1–3 line unfolding/rewriting/witness lemmas (`BlankExtends.refl`, `Tape.move_left_right`, `Tape.move_right_left`, `Tape.mk'_left_right₀`, `Tape.write_self`), meeting the $\ge 30\%$ threshold for **`gemma-first`** routing.
2. **Tier T1 (`pass@1 = 0.0%`, `pass@5 = 0.0%`, mean `171.0 s/decl`)**: `gemma4:12B` is **not effective** on Mathlib's `Primrec`/`Primrec₂` point-free term-combinator proofs (`(list_casesOn .id (const []) (snd.comp snd).to₂).of_eq ...`). Even with `Primrec` combinators retrieved by BM25 and `primrec_tac` imported in the context, `gemma4:12B` repeatedly hallucinated Lean 3 tactic syntax, mismatched `Primrec` vs `Primrec₂` arities, or attempted to call the excluded target lemma itself (caught by the anti-leakage gate). Per the empirical routing rule ($\text{pass@5} < 10\%$), **T1 is routed directly to `frontier`**.
3. **Tier T2 (`pass@1 = 0.0%`, `pass@5 = 0.0%`, mean `298.3 s/decl`)**: `gemma4:12B` is **useless for Tier T2** multi-step inductive simulation, `Nat.rfindOpt`, and `StateTransition` reachability proofs. **T2 is routed directly to `frontier`**.

---

## 2. Anti-Leakage & Verification Protocol

Every benchmark item in `tools/run_calibration.py` enforced four strict anti-leakage barriers:
1. **Retrieval Exclusion (`--exclude`)**: The target declaration, its unqualified/short aliases, and any near-duplicates (`foo'`, `foo_aux`, `Computable.*` counterparts) were excluded from both `RepositoryIndex.retrieve_premises` and `RepositoryIndex.retrieve_accepted_proofs`.
2. **Direct-Call Rejection**: Any candidate proof body referencing any excluded identifier in `--exclude` was rejected prior to compilation (`error: forbidden token '<excluded_lemma>' in candidate proof`).
3. **`@[simp]` Neutralization**: Any target lemma carrying `@[simp]` in Mathlib (`Tape.move_left_right`, `Tape.move_right_left`, `Tape.mk'_right₀`, `Tape.mk'_left_right₀`, `Tape.write_self`, `Tape.write_mk'`, `ListBlank.append_mk`) was stripped of its simp attribute in the spec preamble via `attribute [-simp] <target>`.
4. **Compiler-Verified Acceptance (`lake env lean`)**: A candidate was marked `accepted = true` in `.agents/gemma_usage.jsonl` if and only if `LEAN_NUM_THREADS=2 lake env lean` exited `0` with **zero warnings**, **zero errors**, **zero forbidden tokens** (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`), and a declaration header before `:=` identical to the spec.

---

## 3. Hardware, Context Window & MLX Memory/Swap Telemetry (24 GB Unified RAM)

During calibration we observed that Ollama `0.40.16`'s MLX runner (`gemma4:12B`, 7.7 GB base weights) dynamically expands its unified GPU/RAM buffer up to **16 GB** when kept resident across long multi-turn requests, pushing macOS swap past 11 GB on a 24 GB machine. We progressed through three hardware configurations across the 40 items:

| Phase / Ledger Milestone | Items Covered | `num_ctx` | `MAX_PROMPT_CHARS` | `think` Mode | `keep_alive` | Peak `ollama ps` `SIZE` | Peak `vm.swapusage used` | Post-Batch / Post-Call `ollama ps` & Swap |
|---|---|---|---|---|---|---|---|---|
| Pre-pause smoke (`W0`) | 2 (`T0_01`, `T1_01` smoke) | 32768 | uncapped | `false` (1–3), `true` (4–5) | `"30m"` | 16 GB | ~7,500M | Unloaded before Option 1 |
| Aborted 3-item check (`W0-opt1`) | 3 (`T0_01`–`T0_03` check) | 16384 | 8000 | `false` (1–3), `true` (4–5) | `"30m"` | **16 GB** | **8,247.25M / 9,216.00M** | Paused & unloaded at item 3 per `#51` (`>13 GB` alert) |
| **Batch 1 (`W0-opt1b`)** | **Items `01–10 / 40`** (`T0_01`–`T0_10`) | **8192** | **8000** | **`false` (all 5)** | `"30m"` | **16 GB** (grew from 7.8 GB to 16 GB by item 10) | **11,180.00M / 12,288.00M** | Post-`ollama stop`: `ollama ps` empty, swap `5,876.50M` |
| **Batch 2a (`W0-optA`)** | **Items `11–18 / 40`** (`T0_11`–`T0_15`, `T1_01`–`T1_03`) | **4096** | **4000** | **`false` (all 5)** | `"30m"` | **16 GB** (3-req probe was 10.0 GB; grew to 16 GB by item 18) | ~9,500M | Paused & unloaded at item 18 per `#65`; swap dropped to `2,850.44M` |
| **Batches 2b–4 (`W0-opt2`, Locked Final Config)** | **Items `19–40 / 40`** (`T1_04`–`T1_15`, `T2_01`–`T2_10`) | **4096** | **4000** | **`false` (all 5)** | **`0` (unload after every call)** | **7.7 GB** (during call; `0 GB` / empty immediately after every call) | **3,759.62M / 5,120.00M** | Post-batch `ollama ps` **empty**, swap **`3,215M–3,674M`** (`<= 8,000M`) |

### Key Hardware Finding (`"keep_alive": 0` + `num_ctx: 4096`)
- Locking `"keep_alive": 0` (numeric `0`) in `config/ollama_gemma_config.json` and `tools/ollama_lean4_client.py` forces Ollama to unload the MLX runner immediately after each `/api/chat` response (`load_duration = 1.41 s` from macOS page cache on subsequent calls).
- Under `"keep_alive": 0`, **Ollama and `lake env lean` never coexist in unified RAM**, peak `ollama ps` memory stays at **7.7 GB** during inference (`0 GB` during Lean compilation), and swap stayed strictly between **2,826 MB and 3,760 MB** across all 110 consecutive Ollama + Lean calls of items `19–40`.

---

## 4. Error-Class Breakdown Across the 40-Lemma Benchmark (181 Verified Attempts)

| Error Class | T0 Attempts (56) | T1 Attempts (75) | T2 Attempts (50) | Total Benchmark Attempts (181) | Share of Attempts |
|---|---:|---:|---:|---:|---:|
| `none` (**Accepted by Lean**) | **5** | **0** | **0** | **5** | **2.8%** |
| `other` (incl. anti-leakage self-call rejection, failed `simp`/`rw`, statement edit rejection) | 23 | 30 | 4 | 57 | 31.5% |
| `unknown identifier` | 10 | 10 | 13 | 33 | 18.2% |
| `type mismatch` | 7 | 12 | 12 | 31 | 17.1% |
| `unsolved goals` | 9 | 15 | 7 | 31 | 17.1% |
| `syntax` | 2 | 8 | 14 | 24 | 13.3% |
| `timeout` | 0 | 0 | 0 | 0 | 0.0% |

### Ledger Breakdown by Milestone Tag (`.agents/gemma_usage.jsonl`, 204 Total Rows)

- `W0` (pre-pause 32k-ctx smoke, 2 decls, 10 calls): 1 accepted (`T0_01` pass@1), 9 rejected.
- `W0-opt1` (aborted 16k-ctx check, 3 decls, 11 calls): 1 accepted (`T0_01` pass@1), 10 rejected.
- `W0-opt1b` (Batch 1 items `01–10 / 40`, 8k-ctx, 10 T0 decls, 35 calls): 4 accepted (3 pass@1, 4 pass@5), 31 rejected.
- `W0-optA` (Batch 2a items `11–18 / 40`, 4k-ctx, 5 T0 + 3 T1 decls, 38 calls): 1 accepted (`T0_11` pass@1), 37 rejected.
- `W0-opt2` (Batches 2b–4 items `19–40 / 40`, 4k-ctx + `keep_alive=0`, 12 T1 + 10 T2 decls, 110 calls): 0 accepted, 110 rejected.

---

## 5. `primrec_tac` Evaluation (Requirement 7)

We implemented a bounded-depth combinator macro `primrec_tac` in `tools/primrec_tac.lean` (and verified it compiles with zero warnings under `LEAN_NUM_THREADS=2 lake build --wfail` and passes `tests/test_primrec_tac.py` on product swap, list cons/reverse/tail, `Option.casesOn`, and `Computable.pair` goals).

- **Direct tactic effectiveness on T1 benchmark goals**: `by primrec_tac` directly closes `T1_01` (`Primrec₂.pair`) and `T1_02` (`Primrec₂.comp`) in one line (`2 / 15 = 13.3%` of T1 benchmark items), whereas the remaining 13 T1 items in Mathlib require `.of_eq` pointwise equality reductions (`fun a => by cases ... <;> simp`) or `list_foldr` accumulators beyond pure structural composition.
- **Effect on `gemma4:12B`'s T1 pass rate**: Although `primrec_tac` was imported and opened in the calibration preamble and advertised in `SYSTEM_RULES`, `gemma4:12B` achieved **`0 / 15 (0.0%)`** on T1 (it did not emit `by primrec_tac` on `T1_01` or `T1_02`, preferring multi-line hallucinated term proofs). Therefore, `primrec_tac` is retained in `tools/primrec_tac.lean` as a human/frontier productivity macro for M2/M4 `Primrec` plumbing, not as a means to make `gemma4:12B` reliable on T1.

---

## 6. Complete 40-Lemma Calibration Table

| ID | Tier | Pinned Mathlib Declaration | Run Phase (`num_ctx`) | Outcome | Wall Time | Tokens | Per-Attempt Error Classes |
|---|---|---|---|---|---:|---:|---|
| `T0_01` | `T0` | `Turing.BlankExtends.refl` | W0-opt1b (8192) | **PASS@2** | 37.1 s | 101 | `#1:other, #2:none` |
| `T0_02` | `T0` | `Turing.BlankExtends.trans` | W0-opt1b (8192) | **FAIL(5)** | 134.9 s | 1246 | `#1:type mismatch, #2:other, #3:unsolved goals, #4:unsolved goals, #5:unsolved goals` |
| `T0_03` | `T0` | `Turing.BlankRel.refl` | W0-opt1b (8192) | **FAIL(5)** | 105.8 s | 1038 | `#1:other, #2:other, #3:other, #4:other, #5:unknown identifier` |
| `T0_04` | `T0` | `Turing.BlankRel.symm` | W0-opt1b (8192) | **FAIL(5)** | 69.4 s | 425 | `#1:syntax, #2:type mismatch, #3:type mismatch, #4:other, #5:type mismatch` |
| `T0_05` | `T0` | `Turing.ListBlank.exists_cons` | W0-opt1b (8192) | **FAIL(5)** | 115.1 s | 806 | `#1:unknown identifier, #2:unknown identifier, #3:unknown identifier, #4:other, #5:unknown identifier` |
| `T0_06` | `T0` | `Turing.Tape.move_left_right` | W0-opt1b (8192) | **PASS@1** | 28.5 s | 60 | `#1:none` |
| `T0_07` | `T0` | `Turing.Tape.move_right_left` | W0-opt1b (8192) | **PASS@1** | 13.6 s | 60 | `#1:none` |
| `T0_08` | `T0` | `Turing.Tape.mk'_right₀` | W0-opt1b (8192) | **FAIL(5)** | 101.4 s | 640 | `#1:other, #2:other, #3:other, #4:other, #5:other` |
| `T0_09` | `T0` | `Turing.Tape.mk'_left_right₀` | W0-opt1b (8192) | **PASS@1** | 22.0 s | 84 | `#1:none` |
| `T0_10` | `T0` | `Turing.Tape.exists_mk'` | W0-opt1b (8192) | **FAIL(5)** | 82.8 s | 378 | `#1:type mismatch, #2:type mismatch, #3:type mismatch, #4:unsolved goals, #5:unsolved goals` |
| `T0_11` | `T0` | `Turing.Tape.write_self` | W0-optA (4096) | **PASS@1** | 12.6 s | 52 | `#1:none` |
| `T0_12` | `T0` | `Turing.Tape.write_mk'` | W0-optA (4096) | **FAIL(5)** | 73.7 s | 512 | `#1:other, #2:unsolved goals, #3:unsolved goals, #4:other, #5:unsolved goals` |
| `T0_13` | `T0` | `Turing.Tape.map_mk'` | W0-optA (4096) | **FAIL(5)** | 77.9 s | 476 | `#1:other, #2:other, #3:other, #4:syntax, #5:other` |
| `T0_14` | `T0` | `Turing.TM0.univ_supports` | W0-optA (4096) | **FAIL(5)** | 98.3 s | 697 | `#1:unknown identifier, #2:unknown identifier, #3:unknown identifier, #4:unknown identifier, #5:unknown identifier` |
| `T0_15` | `T0` | `Computable.const` | W0-optA (4096) | **FAIL(5)** | 39.4 s | 306 | `#1:unsolved goals, #2:other, #3:other, #4:other, #5:other` |
| `T1_01` | `T1` | `Primrec₂.pair` | W0-optA (4096) | **FAIL(5)** | 73.4 s | 711 | `#1:unsolved goals, #2:unknown identifier, #3:unknown identifier, #4:unknown identifier, #5:unknown identifier` |
| `T1_02` | `T1` | `Primrec₂.comp` | W0-optA (4096) | **FAIL(5)** | 193.4 s | 1582 | `#1:unsolved goals, #2:type mismatch, #3:type mismatch, #4:other, #5:unknown identifier` |
| `T1_03` | `T1` | `Primrec.option_bind₁` | W0-optA (4096) | **FAIL(5)** | 94.1 s | 793 | `#1:unsolved goals, #2:other, #3:syntax, #4:type mismatch, #5:other` |
| `T1_04` | `T1` | `Primrec.option_map₁` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 166.9 s | 950 | `#1:other, #2:type mismatch, #3:type mismatch, #4:type mismatch, #5:type mismatch` |
| `T1_05` | `T1` | `Primrec.option_getD_default` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 287.5 s | 2071 | `#1:unsolved goals, #2:unsolved goals, #3:other, #4:unknown identifier, #5:syntax` |
| `T1_06` | `T1` | `Primrec.option_isSome` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 198.9 s | 1098 | `#1:other, #2:syntax, #3:syntax, #4:other, #5:other` |
| `T1_07` | `T1` | `Primrec.nat_double` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 252.9 s | 2176 | `#1:unsolved goals, #2:unsolved goals, #3:unsolved goals, #4:unsolved goals, #5:unsolved goals` |
| `T1_08` | `T1` | `Primrec.nat_double_succ` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 114.8 s | 268 | `#1:other, #2:other, #3:other, #4:other, #5:other` |
| `T1_09` | `T1` | `Primrec.list_head?` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 157.0 s | 562 | `#1:other, #2:unsolved goals, #3:unsolved goals, #4:unsolved goals, #5:type mismatch` |
| `T1_10` | `T1` | `Primrec.list_tail` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 116.8 s | 304 | `#1:other, #2:other, #3:other, #4:unsolved goals, #5:other` |
| `T1_11` | `T1` | `Primrec.list_concat` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 174.2 s | 854 | `#1:other, #2:type mismatch, #3:other, #4:other, #5:unsolved goals` |
| `T1_12` | `T1` | `Primrec.list_flatMap` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 268.7 s | 1595 | `#1:unknown identifier, #2:other, #3:type mismatch, #4:type mismatch, #5:type mismatch` |
| `T1_13` | `T1` | `Primrec.list_length` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 134.3 s | 699 | `#1:other, #2:other, #3:other, #4:other, #5:other` |
| `T1_14` | `T1` | `Turing.ListBlank.append_mk` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 178.6 s | 921 | `#1:other, #2:other, #3:syntax, #4:other, #5:syntax` |
| `T1_15` | `T1` | `Turing.Tape.map_move` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 154.2 s | 571 | `#1:unknown identifier, #2:syntax, #3:unknown identifier, #4:unknown identifier, #5:syntax` |
| `T2_01` | `T2` | `Primrec.nat_iterate` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 337.6 s | 2176 | `#1:unknown identifier, #2:unsolved goals, #3:unsolved goals, #4:unknown identifier, #5:unsolved goals` |
| `T2_02` | `T2` | `Primrec.dom_finite` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 238.9 s | 1892 | `#1:syntax, #2:type mismatch, #3:unknown identifier, #4:unknown identifier, #5:syntax` |
| `T2_03` | `T2` | `Primrec.list_drop` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 250.0 s | 1435 | `#1:type mismatch, #2:unsolved goals, #3:unsolved goals, #4:unknown identifier, #5:unknown identifier` |
| `T2_04` | `T2` | `Partrec.rfindOpt` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 257.8 s | 2176 | `#1:type mismatch, #2:type mismatch, #3:type mismatch, #4:type mismatch, #5:type mismatch` |
| `T2_05` | `T2` | `Nat.rfindOpt_mono` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 250.8 s | 1297 | `#1:other, #2:unknown identifier, #3:type mismatch, #4:unknown identifier, #5:type mismatch` |
| `T2_06` | `T2` | `Nat.Partrec.Code.encode_lt_comp` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 318.7 s | 2176 | `#1:syntax, #2:syntax, #3:syntax, #4:syntax, #5:other` |
| `T2_07` | `T2` | `StateTransition.reaches_eval` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 348.4 s | 2176 | `#1:syntax, #2:syntax, #3:syntax, #4:syntax, #5:syntax` |
| `T2_08` | `T2` | `StateTransition.tr_eval` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 311.1 s | 1740 | `#1:type mismatch, #2:unknown identifier, #3:unsolved goals, #4:type mismatch, #5:type mismatch` |
| `T2_09` | `T2` | `Turing.TM0.step_supports` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 320.2 s | 2014 | `#1:other, #2:syntax, #3:syntax, #4:other, #5:syntax` |
| `T2_10` | `T2` | `Turing.TM0.Machine.map_step` | W0-opt2 (4096, keep_alive=0) | **FAIL(5)** | 349.0 s | 2176 | `#1:unknown identifier, #2:unsolved goals, #3:unknown identifier, #4:unknown identifier, #5:unknown identifier` |
