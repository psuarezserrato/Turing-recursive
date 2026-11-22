# Final Audit — TuringRecursive (`TM → Partrec`)

- **Audited commit**: `main` @ `6910013` (library unchanged by this document).
- **Auditors**: (1) per-milestone verifier, Gates G1–G8 on each worktree before merge (M1–M6, all PASS);
  (2) an independent adversarial final auditor that did not build the code (this audit), plus the
  coordinator's structural checks.
- **Toolchain**: Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- **Overall verdict**: **PASS-WITH-RISKS.** Mathematical soundness, statement faithfulness,
  anti-vacuity and downstream usability: **PASS, 0 blockers.** Repository hygiene and
  reproducibility of the provenance gate (G8): **FAIL on 3 MAJOR items, all outside the Lean library
  and all cheap to fix** (see §4). Nothing found weakens any theorem.

## 1. Soundness — PASS

| Check | Result |
|---|---|
| `LEAN_NUM_THREADS=2 lake build --wfail` | exit 0, 1,846 jobs, 0 warnings, 0 errors |
| `tools/collect_axioms.sh` | 0 forbidden tokens in 8 files; 235/235 public declarations ⊆ {`propext`, `Classical.choice`, `Quot.sound`} |
| Independent string-aware, nested-comment-stripped scan | 0 × `sorry admit axiom unsafe implemented_by native_decide opaque maxHeartbeats set_option` |
| Independent kernel audit of **all 343** `TuringRecursive.*` constants (incl. 108 internal ones the project tool skips) | 0 disallowed axioms |
| `#lint+` (15 linters) and `#lint only docBlameThm` over 186 declarations (+157 auto-generated) | 0 errors |
| Line width | max 100 columns, 0 lines over |
| Python tool tests (`python3 -m unittest discover -s tests`) | 12/12 pass |

**Use of choice.** Nine declarations are `noncomputable`: `codeStateFinset`, `instFintypeCodeTM0Λ`,
`instDecidableEqCodeTM0Λ` (`Classical.decEq`), `codeTM0`, `TM0Code.compile`, `univCode`, `UniversalΛ`,
its three instances, and `U`. They come from eliminating Mathlib's `Prop`-valued
`Nat.Partrec`/`exists_code` statements. All *encodings and syntax* (`ListBlank.trim`,
`TM0Code.machine`, `encNat`, `decNat`, `encUniv`, `decUniv`, every `Primcodable` instance) are
computable (checked with `#eval`) and are fixed **before** any choice is made, so choice cannot
smuggle in a halting oracle. This is the standard, accepted consequence of Mathlib's own
`exists_code`; it is not a defect, but it is noted for readers who expect an explicit `U`.

## 2. Statement faithfulness vs. the frozen specification — PASS

- Frozen spec: tag `gate-s1-frozen` (`7a055ce`), `spec/Spec.lean` SHA-256
  `b9ee4acddccaaadf68471374b570fd783e95dded44ac429183edc76e43afeb3a`, 89 declarations.
- **89/89 headers match the library byte-for-byte** (names, namespaces, attributes,
  `scoped`/plain, universes, hypotheses, conclusions): 0 missing, 0 extra hypotheses.
- Docstrings: 58 identical; 31 helper theorems gained docstrings (to satisfy `docBlameThm`); no
  existing docstring changed.
- The only body differences (5 declarations: `UniversalΛ`, its three instances, `U`) implement the
  **user-approved S1 decision Q4** (`codeTM0Λ univCode` / `codeTM0 univCode` instead of
  `exists_universal_tm0.choose…`).
- The spec file itself is intentionally **not** on `main` (it contains `sorry`); it is preserved on
  branch `work/spec` and the tag.

## 3. Completeness vs. `MISSION_DIRECTIVE.md` — PASS (T-F deferred by decision)

| Item | Status | File |
|---|---|---|
| T-B generic `StateTransition.eval` partrec, parametrized version, `Reaches ↔ ∃n iterate` | Delivered | `Eval.lean` |
| E: `Primrec` of `rdropWhile`/`dropLast`; `ListBlank.trim`; scoped `Primcodable` for `Dir`, `Stmt`, `ListBlank`, `Tape`, `Cfg`; `Primrec` API; round-trips | Delivered | `ListPrimrec.lean`, `Encoding.lean` |
| T-A fixed machine: `step_primrec(_of_primrec)`, `evalCfg_partrec`, `eval_partrec` | Delivered | `TM0Eval.lean` |
| T-A′ Kleene form `∃ c, c.eval (encode l) = (TM0.eval M l).map encode` | Delivered | `TM0Eval.lean` |
| T-C uniform `TM0Code`, `step_primrec`, `eval_partrec`, injective pointed relabeling | Delivered (strengthened: injectivity) | `Uniform.lean` |
| T-D `nat_partrec_iff_exists_tm0` with fixed `Γ₀`, named `encNat`/`decNat` | Delivered | `Equivalence.lean` |
| T-E(1) halting r.e. and not computable; (2) primitive-recursive compiler; (3) universal `U` with exact output tape | Delivered (+ `eval_compile_nat`, Q3) | `Universal.lean` |
| T-F (TM1/TM2) | **Deferred by user decision Q4** | — |
| §2.10 `Computable.iterate`, `Primrec.dite` | Dropped by user decision (unneeded) | — |

Gates G1–G7 were verified directly on `main` (10/10 `#audit_wiring` checks across M1–M6 were
non-decorative). G8 holds only as noted in F-02/F-03.

## 4. Semantic anti-vacuity — PASS

A 290-line adversarial suite (compiled with warnings-as-errors, then deleted) checked that no
statement is trivially true/false:

- `nat_partrec_iff_exists_tm0`: `Λ` is `Fintype` (blocks infinite-state oracle machines); `Γ₀`
  and `encNat` are concrete; `codeTM0 succ` maps `encNat 41 ↦ encNat 42`.
- `TM0Code.exists_relabeling`: on a bit-flipper, `f true ≠ 0`, `g true ≠ 0`, and results on
  `[]` and `[f true]` differ — the constant-0 collapse the S1 review caught is refuted.
- Halting (`halting_re` ∧ `¬ ComputablePred`) proved together; looping machines give `¬ Dom`
  for `eval`, `compile`, and `U`; non-decoding naturals give `Part.none` (`eval_compile_nat`).
- `encNat`/`decNat`: `n = 0`, `n = 65537`, trailing blanks, and the prefix case
  `encNat 1 <+: encNat 2`; the window `[0, L]` (including the blank at cell `L`) uniquely isolates
  the output — `[0, L-1]` does not. This directly informs CMPP B2.
- Downstream: a throw-away Lake project with `[[require]]` on this repo plus TauCeti built
  (1,849 jobs, no manifest/scope conflicts).

## 5. Findings

| ID | Sev | Area | Finding | Recommended fix | Status |
|---|---|---|---|---|---|
| F-01 | MAJOR | Licensing | All 7 library headers say "Apache 2.0 … file LICENSE"; no `LICENSE` file exists. | Add Apache-2.0 `LICENSE`. | **Open** |
| F-02 | MAJOR | Reproducibility / G8 | `.agents/gemma_accepted/`, `.agents/gemma_escalations/` are untracked; `gemma_usage.jsonl` is git-ignored; on a clean clone G8 fails (45/45 violations), and `check_gemma_provenance.py` defaults to tiers `T0,T1` (60 violations) although routing says T0 only. | Commit the artifacts (after F-03) and default `--tiers` to `T0`; or document G8 as a pre-merge gate. | **Open** |
| F-03 | MAJOR | Tooling | `sanitize_decl_filename` strips non-ASCII, so `gammaPrimeEquivFin4_consₗ` and `…_cons` share one artifact file (25 files for 26 accepted T0 declarations); one stale escalation JSON (`kPrimeEquivFin4_main`); checker does not verify the declaration name inside the artifact. | Hash-suffix non-ASCII names; clear stale escalations; verify the name inside the artifact. | **Open** |
| F-04 | MINOR | Portability | `bootstrap_worktree.sh` and four Python tools hard-code `/Users/pablosuarez/Desktop/Turing-recursive`; `bootstrap_worktree.sh` tests for a `TauCeti` dir that does not exist here; stale `S1` contract path; string-unaware comment stripper. | Resolve root with `git rev-parse --git-common-dir`; fix the checks. | **Open** |
| F-05 | MINOR | Docs/branches | `docs/routing.md` cites `tm0_halting_*` (actual `TM0Code.halting_*`) and omits `ListPrimrec.lean`; rules/config text still mention S4TuringPoisson/TauCeti; README is 6 lines; 7 merged `work/*` branches remain. | Edit docs; `git branch -d` merged branches (keep `work/spec`, tag). | **Open** |
| F-06 | MINOR | Upstreamability | `explicitVarsOfIff` flags `TM0.step_eq_none_iff`, `trCfg_halt_singleton_iff`, `U_mem_evalCfg_iff`; `List.dropLast_eq_rdrop` duplicates `List.dropLast_eq_take`; no `DecidableEq` on `ListBlank`/`Tape`/`Cfg`. | Address when preparing Mathlib PRs (without touching frozen signatures on `main`). | Deferred |
| F-07 | INFO | CMPP | `U`/`compile` are `noncomputable`; output length `L(c')` depends on `c'`; `Γ₀` instances are `scoped`. | In S4TP: `open scoped TuringRecursive`; apply planned refactor I2 (variable-radius cylinders including cell `L`). | Noted |
| F-08 | INFO | Tooling | `tools/audit_axioms.lean` skips `isInternal` constants (108 here; independently verified clean). | Test module membership before the internal filter. | Noted |

**Not verified by the auditor**: Mathlib-only linters outside the 1,846-job build closure; a live
re-run of the local-model benchmark (checked offline from the ledger); a network `git clone`
(no remote is configured).

## 6. Local-model (`gemma4:12B`) provenance — figures as measured

- Ledger: 391 verified calls, 0 unverified; accepted 33 (31 declarations incl. calibration).
- Library T0 declarations: **45 checked, 26 accepted by the local model (57.8%), 19 escalated after
  5 logged compiler failures (42.2%), 0 gate violations.**
- Library total ≈ 179 new public declarations, so the local model produced ≈ 15% of them, all
  simple unfolding/projection/round-trip lemmas; **none of the headline theorems.** T1/T2
  declarations were routed to the frontier model directly, because the calibration measured 0%
  for both tiers (see the technical report).

## 7. Recommendation

Accept the library as complete and correct for its stated scope. Before using the repository as a
dependency of S4TuringPoisson (or publishing it), apply F-01…F-05 (about an hour of work; none
touches Lean code). F-06 is for the Mathlib PR stage.
