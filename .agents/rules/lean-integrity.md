---
trigger: always_on
description: "Mandatory Lean 4 kernel, axiom, LSP-first, anti-vacuity, and 24GB Unified RAM swap-prevention invariants for TuringRecursive."
---

# TuringRecursive Non-Negotiable Formalization & Hardware Rules

- **Zero Sorry / Zero Custom Axioms**: No merged file may contain `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by`. Every headline theorem must pass `#print axioms` showing strictly a subset of `{propext, Classical.choice, Quot.sound}`.
- **LSP-First Proof Loop**: Query `lean_goal` and `lean_diagnostic_messages` first, search Mathlib and TauCeti via `lean_local_search` and `lean_loogle` before inventing definitions, and test tactics with `lean_multi_attempt`. Pass `--commit=never` if invoking `autoprove` inside a worker worktree prior to verifier sign-off.
- **24GB Unified RAM & `gemma4:12B` Guardrails (Anti-Swap)**:
  - Always export `LEAN_NUM_THREADS=2` and pass `--wfail` to `lake build` (`LEAN_NUM_THREADS=2 lake build --wfail`; Lake 5.0.0 has no `-j` flag) so C++ Lean elaboration threads do not contend with Metal/MLX `gemma4:12B` unified memory bandwidth.
  - Keep at most **1–2 active Lean LSP / `lake` workers** running concurrently; all other workers must remain parked (`waiting`).
  - Route Phase 0 search helpers, discrete `GeneralizedShift` / `TM0` lemmas, and routine diagnostic/linter fixes to local headless `gemma4:12B` (`tools/ollama_lean4_client.py`, locked to `num_ctx=16384`, `max_prompt_chars=8000`, `OLLAMA_NUM_PARALLEL=1`, `temperature=1.0`, `top_p=0.95`, `top_k=64`, `think=false` on search/routine edits).
  - Keep `Interfaces.lean`, Verifiers (`@verifier-geom`, `@verifier-comp`), $S^4$ stereographic `mfderiv` charts, and `SmoothForm` pullback proofs on **Gemini 4 Carbon**.
  - **5-Retry Escalation Rule**: Escalate any subgoal failing **>5** `lean_multi_attempt` / `gemma4:12B` tactic cycles immediately to **Gemini 4 Carbon** rather than looping locally on manifold lemma names.
- **Junk-Value Vigilance**: Mathlib's `mfderiv`, `fderiv`, `VectorField.mpullback`, and division by zero evaluate to `0` when differentiability or invertibility hypotheses fail. Every definition or theorem using derivatives or top-form division must carry explicit smoothness/nowhere-vanishing hypotheses and a concrete non-zero `Checks` witness.
- **Anti-Suspension & Anti-Vacuity**:
  - Never prove 4-manifold Turing completeness via topological 3D suspension (`S^3 x (-1,1)`); the diffeomorphism MUST preserve the symplectic foliation and global unimodular volume form of the generically rank-2 Jacobian-Poisson structure `pi_f`.
  - Never allow `IsTuringComplete` to construct `(p, U)` via `Classical.by_cases` on halting: `encodePoint` depends ONLY on `(M, inputTape)` (with computable rational approximations) and `encodeOpen` depends ONLY on `(M, k, targetWindow)` with `U` proved nonempty.
- **Exclusive File Ownership**: Edit only files inside your assigned `.worktrees/<worker>/TuringRecursive/<Subdir>/` boundary. Propose cross-module signature updates to `@coordinator` on the Shared Message Board.
