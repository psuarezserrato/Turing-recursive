---
trigger: always_on
description: "Mandatory Lean 4 kernel, axiom, LSP-first, anti-vacuity, and 24GB Unified RAM swap-prevention invariants for TuringRecursive."
---

# TuringRecursive Non-Negotiable Formalization & Hardware Rules

- **Zero Sorry / Zero Custom Axioms**: No merged file may contain `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by`. Every headline theorem must pass `#print axioms` showing strictly a subset of `{propext, Classical.choice, Quot.sound}`.
- **LSP-First Proof Loop**: Query `lean_goal` and `lean_diagnostic_messages` first, search Mathlib via `lean_local_search` and `lean_loogle` before inventing definitions, and test tactics with `lean_multi_attempt`. Pass `--commit=never` if invoking `autoprove` inside a worker worktree prior to verifier sign-off.
- **24GB Unified RAM & `gemma4:12B` Guardrails (Anti-Swap)**:
  - Always export `LEAN_NUM_THREADS=2` and pass `--wfail` to `lake build` (`LEAN_NUM_THREADS=2 lake build --wfail`; Lake 5.0.0 has no `-j` flag) so C++ Lean elaboration threads do not contend with Metal/MLX `gemma4:12B` unified memory bandwidth.
  - Keep at most **1–2 active Lean LSP / `lake` workers** running concurrently; all other workers must remain parked (`waiting`).
  - Route `-- tier: T0` (`gemma-first`) boilerplate, simp wrappers, and round-trip lemmas to local headless `gemma4:12B` (`tools/gemma_loop.py` / `tools/ollama_lean4_client.py`, locked to `num_ctx=4096`, `max_prompt_chars=4000`, `keep_alive=0`, `OLLAMA_NUM_PARALLEL=1`, `temperature=1.0`, `top_p=0.95`, `top_k=64`, `think=false`).
  - Keep core `Partrec`/`StateTransition`/`TM0` proofs, verifiers (`@verifier-tm`), and Mathlib-PR-quality interface signatures on **Gemini 4 Carbon**.
  - **5-Retry Escalation Rule**: Escalate any subgoal failing **>5** `lean_multi_attempt` / `gemma4:12B` tactic cycles immediately to **Gemini 4 Carbon** with its logged `.agents/gemma_escalations/<decl>.json` record.
- **Anti-Vacuity & Mathlib-PR Discipline**:
  - Tape alphabets for universal/equivalence theorems (`Γ₀`) and encodings (`encNat`, `decNat`, `encUniv`, `decUniv`) must be concrete and computable, with explicit round-trip and non-collapse (`TM0Code.exists_relabeling` injectivity) theorems verified by tests.
  - Enforce `autoImplicit = false`, `relaxedAutoImplicit = false`, `max 100` columns, `#lint+`, and `docBlameThm`.
- **Exclusive File Ownership**: Edit only files inside your assigned `.worktrees/<worker>/` boundary. Propose cross-module signature updates to `@coordinator` on the Shared Message Board.
