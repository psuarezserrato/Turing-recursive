# Turing-recursive (`TuringRecursive`)

Lean 4 / Mathlib-PR-quality formalization proving the missing **TM → Partrec** direction (and its uniform and universal corollaries) alongside Mathlib's `Partrec → TM` pipeline.

- **Lean toolchain**: `v4.36.0` (`autoImplicit = false`, `relaxedAutoImplicit = false`)
- **Mathlib pin**: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
- **License**: GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use ([LICENSE.md](LICENSE.md))

## Scope & Modules

| Module | Deliverables | Summary |
|---|---|---|
| `TuringRecursive/Eval.lean` | **T-B** | Generic `StateTransition.eval_partrec`, `eval_partrec₂` (cross-universe), `reaches_iff_exists_iterate` |
| `TuringRecursive/ListPrimrec.lean` | **E (List)** | `Primrec` for `List.rdropWhile` and `List.dropLast` |
| `TuringRecursive/Encoding.lean` | **E (Tape/Cfg)** | `ListBlank.trim`, scoped diamond-free `Primcodable` (`Dir`, `TM0.Stmt`, `ListBlank`, `Tape`, `TM0.Cfg`), `_root_.Primrec.listBlank_*` & `tape_*`, round-trips |
| `TuringRecursive/TM0Eval.lean` | **T-A, T-A′** | Fixed-machine `TM0.step_primrec_of_primrec`, choice-free `TM0.step_primrec`, `evalCfg_partrec`, `eval_partrec`, Kleene `exists_code_eval` |
| `TuringRecursive/Uniform.lean` | **T-C** | Uniform finite code `TM0Code`, `instPrimcodableTM0Code`, `TM0Code.step_primrec`, `TM0Code.eval_partrec`, injective pointed relabeling `TM0Code.exists_relabeling` |
| `TuringRecursive/Equivalence.lean` | **T-D** | Fixed 1,250-symbol alphabet `Γ₀`, computable `encNat`/`decNat`, `default_notMem_encNat`, `nat_partrec_iff_exists_tm0` |
| `TuringRecursive/Universal.lean` | **T-E(1)–(3)** | `TM0Code.halting_re`, `TM0Code.halting_not_computable`, compiler `TM0Code.compile` (`eval_compile_nat`, `eval_compile`), explicit universal machine `(UniversalΛ, U)` & `U_evalCfg_tape` |
| `TuringRecursive.lean` | Root | Re-exports all public modules (`T-F` TM1/TM2 deferred by decision) |

## Downstream Usage

In another Lean 4 Lake project (using the same Lean/Mathlib pin), add `TuringRecursive` to `lakefile.toml` and open the scoped `Primcodable` / `Γ₀` instances where needed:

```lean
import TuringRecursive

open TuringRecursive
open scoped TuringRecursive
```

(`instPrimcodableTM0Code`, `UniversalΛ`, and `UniversalΛ`'s `Fintype`/`DecidableEq`/`Inhabited` instances are plain non-scoped instances.)

## Build, Audit, and Tests

```bash
LEAN_NUM_THREADS=2 lake build --wfail
bash tools/collect_axioms.sh
python3 -m unittest discover -s tests -v
python3 tools/check_gemma_provenance.py 302796b..HEAD
```

## Documentation & Reports

- [MISSION_DIRECTIVE.md](MISSION_DIRECTIVE.md) — Mission specification and deliverables
- [docs/S1_statements.md](docs/S1_statements.md) — Frozen Gate S1 interface specification (89 declarations; spec stub retained on `gate-s1-frozen`)
- [docs/routing.md](docs/routing.md) & [docs/gemma_calibration.md](docs/gemma_calibration.md) — Empirical `gemma4:12B` calibration & routing policy
- [docs/AUDIT.md](docs/AUDIT.md) — Independent adversarial audit (G1–G8, anti-vacuity, axiom closure)
- [docs/TECHNICAL_REPORT.md](docs/TECHNICAL_REPORT.md) — Full mathematical & engineering technical report
- [docs/EXECUTIVE_REPORT.md](docs/EXECUTIVE_REPORT.md) — Executive summary

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](LICENSE.md) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
