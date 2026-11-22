# TuringRecursive — Executive Report

## Outcome

We formally proved, in Lean 4 with Mathlib, that **everything a Turing machine computes is
computable by a recursive function — for all machines at once** — and the converse, with no unproved
assumptions. This closes a real gap in Mathlib (it had only the converse direction) and unblocks the
S4TuringPoisson research program (a universal machine realized as a Hamiltonian flow on S⁴), which
was waiting on it.

## What exists now

- **8 Lean files, ~2,060 lines**, building cleanly with warnings treated as errors.
- **Machine-checked** by Lean's kernel; the only axioms used are the three standard ones
  (excluded middle/choice, propositional and quotient extensionality). No `sorry`.
- **Headline results**: Turing-machine evaluation is partial recursive (any fixed machine, and
  uniformly in a machine code); recursive functions = finite-state Turing machines over a fixed
  alphabet; halting is undecidable; there is **one universal machine** whose output is read off
  exactly from its tape.
- **Frozen contract**: the 89 statements you reviewed and approved match the final code
  character-for-character.

## How we know it is right

1. Statements were written first, reviewed by you, and frozen (tag `gate-s1-frozen`).
2. Each of six milestones was checked by a separate verifier on eight gates (build, axioms,
   statement match, genuine proof dependencies, adversarial sanity tests, faithfulness, honest
   labels, provenance).
3. A final independent auditor rebuilt everything, re-audited all 343 kernel constants, tried to
   make statements trivially true or false, and tested the library as a dependency of the next
   project. **No soundness or statement defect was found.** The review at S1 caught one real flaw in
   the original plan (a relabeling theorem that could be satisfied by erasing the machine); it was
   fixed before any proof work.

## Honest status

| Area | Status |
|---|---|
| Mathematics and statements | Complete, verified |
| Scope | TM0 only; TM1/TM2 deferred by your decision |
| Repository hygiene | **3 major, small, non-mathematical items open**: no `LICENSE` file; local-model provenance files not yet committed; a filename collision in the provenance tool. Plus minor items (hard-coded paths, doc names). About an hour to fix; none touches the Lean code. |

## The local model (gemma4:12B), plainly

It was calibrated first, and the result decided how it was used. It proves short rewrite and
unfolding lemmas (calibration: 33% within five tries) and fails on everything harder (0%). In the
library it produced **26 of 45** of the easy lemmas (about **15% of all declarations**) and none
of the main theorems; the rest, including all difficult proofs, came from the frontier model. A
memory leak in the local runtime (7.7 GB growing to 16 GB, heavy swapping) was found and fixed by
unloading the model after every call. The local model saved some frontier effort on boilerplate; it
did not change the critical path.

## Decisions for you

1. Apply the hygiene fixes (F-01…F-05 in `docs/AUDIT.md`) now? Recommended before S4TuringPoisson
   depends on this repository.
2. Proceed to the CMPP mission in S4TuringPoisson (now unblocked), or first prepare the Mathlib
   pull requests (three-part split ready)?
3. Do you want T-F (TM1/TM2 versions) scheduled?

## Where to look

`docs/AUDIT.md` (audit and findings) · `docs/TECHNICAL_REPORT.md` (theorems, proofs, limits) ·
`docs/S1_statements.md` (reviewed statements) · `docs/gemma_calibration.md`, `docs/routing.md`.
