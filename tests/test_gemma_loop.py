import json
import tempfile
import unittest
from pathlib import Path
import sys

TOOLS_DIR = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import gemma_loop
import index as bm25_index


class TestGemmaLoop(unittest.TestCase):
    def test_validate_and_splice_rejects_statement_modification(self):
        spec_src = (
            "namespace Foo\n"
            "-- tier: T0\n"
            "theorem add_zero_custom (n : Nat) : n + 0 = n := by\n"
            "  sorry\n"
            "end Foo\n"
        )
        decls = gemma_loop.parse_spec_declarations(spec_src)
        self.assertEqual(len(decls), 1)
        d = decls[0]
        self.assertEqual(d.name, "Foo.add_zero_custom")
        self.assertEqual(d.tier, "T0")
        self.assertTrue(d.has_sorry)

        # 1. Exact statement match succeeds
        ok, spliced, _ = gemma_loop.validate_and_splice_candidate(
            d,
            "theorem add_zero_custom (n : Nat) : n + 0 = n := by\n  rfl",
        )
        self.assertTrue(ok)
        self.assertTrue(spliced.startswith("theorem add_zero_custom (n : Nat) : n + 0 = n :="))

        # 2. Proof-only response succeeds and preserves statement byte-for-byte
        ok2, spliced2, _ = gemma_loop.validate_and_splice_candidate(d, "rfl")
        self.assertTrue(ok2)
        self.assertTrue(spliced2.startswith("theorem add_zero_custom (n : Nat) : n + 0 = n :="))

        # 3. Altered statement is rejected
        ok3, reason, _ = gemma_loop.validate_and_splice_candidate(
            d,
            "theorem add_zero_custom (n : Nat) : True := by\n  trivial",
        )
        self.assertFalse(ok3)
        self.assertIn("modified", reason)

        # 4. Prompt size cap MAX_PROMPT_CHARS = 8000 is enforced
        huge_ctx = " -- " + ("x" * 12000)
        msgs = gemma_loop.build_prover_messages(d, huge_ctx, [], [], attempt=1)
        self.assertLessEqual(len(msgs[1]["content"]), gemma_loop.MAX_PROMPT_CHARS)

        # 5. Indentation-only differences on multiline statements are accepted and spliced with exact spec bytes
        spec_multi = (
            "theorem multi_thm (n : Nat) :\n"
            "    n + 0 = n := by\n"
            "  sorry\n"
        )
        d_multi = gemma_loop.parse_spec_declarations(spec_multi)[0]
        ok_indent, spliced_indent, _ = gemma_loop.validate_and_splice_candidate(
            d_multi,
            "theorem multi_thm (n : Nat) :\n        n + 0 = n := by\n  rfl",
        )
        self.assertTrue(ok_indent)
        self.assertTrue(spliced_indent.startswith("theorem multi_thm (n : Nat) :\n    n + 0 = n :="))

    def test_prove_spec_file_accept_and_escalate(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.toml").write_text('name = "TuringRecursive"\n', encoding="utf-8")
            spec_path = root / "spec.lean"
            spec_path.write_text(
                "-- tier: T0\n"
                "theorem easy_thm (n : Nat) : n = n := by\n"
                "  sorry\n\n"
                "-- tier: T1\n"
                "theorem hard_thm (n : Nat) : n + 1 = 1 + n := by\n"
                "  sorry\n",
                encoding="utf-8",
            )

            empty_bm25 = bm25_index.InvertedBM25()
            dummy_idx = bm25_index.RepositoryIndex(empty_bm25, empty_bm25, root)

            think_history = []

            def fake_model_caller(**kwargs):
                decl_name = kwargs.get("declaration")
                attempt = kwargs.get("attempt")
                think = kwargs.get("think")
                think_history.append((decl_name, attempt, think))
                if decl_name == "easy_thm":
                    if attempt == 1:
                        return {
                            "status": "success",
                            "model": "gemma4:12B",
                            "elapsed_ms": 10.0,
                            "eval_count": 12,
                            "lean_code": "theorem easy_thm (n : Nat) : n = n := by\n  bad_tactic",
                        }
                    return {
                        "status": "success",
                        "model": "gemma4:12B",
                        "elapsed_ms": 12.0,
                        "eval_count": 10,
                        "lean_code": "theorem easy_thm (n : Nat) : n = n := by\n  rfl",
                    }
                else:
                    return {
                        "status": "success",
                        "model": "gemma4:12B",
                        "elapsed_ms": 15.0,
                        "eval_count": 20,
                        "lean_code": "theorem hard_thm (n : Nat) : n + 1 = 1 + n := by\n  rfl",
                    }

            def fake_lean_checker(scratch_path: Path, _repo_root: Path, _timeout: float):
                txt = scratch_path.read_text(encoding="utf-8")
                if "bad_tactic" in txt:
                    return False, 1, "error: unknown tactic 'bad_tactic'", 5.0, False
                if "theorem hard_thm" in txt:
                    return False, 1, "error: type mismatch", 5.0, False
                if "theorem easy_thm (n : Nat) : n = n :=" in txt and "rfl" in txt:
                    return True, 0, "", 5.0, False
                return False, 1, "error: type mismatch", 5.0, False

            ledger_path = root / ".agents" / "gemma_usage.jsonl"
            res = gemma_loop.prove_spec_file(
                spec_path=spec_path,
                repo_root=root,
                max_attempts=5,
                milestone="W0",
                idx=dummy_idx,
                model_caller=fake_model_caller,
                lean_checker=fake_lean_checker,
                ledger_path=ledger_path,
            )

            self.assertEqual(res["total_sorry_declarations"], 2)
            self.assertEqual(res["accepted_count"], 1)
            self.assertEqual(res["escalated_count"], 1)

            # Verify think=False on all 5 attempts under Option 1b
            hard_thinks = [th for (d, _a, th) in think_history if d == "hard_thm"]
            self.assertEqual(hard_thinks, [False, False, False, False, False])

            # Verify artifacts exist
            self.assertTrue((root / ".agents" / "gemma_accepted" / "easy_thm.lean").is_file())
            esc_path = root / ".agents" / "gemma_escalations" / "hard_thm.json"
            self.assertTrue(esc_path.is_file())
            esc_data = json.loads(esc_path.read_text(encoding="utf-8"))
            self.assertEqual(len(esc_data["attempts"]), 5)


if __name__ == "__main__":
    unittest.main()
