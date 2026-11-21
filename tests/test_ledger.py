import tempfile
import unittest
from pathlib import Path
import sys

TOOLS_DIR = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import ledger


class TestLedger(unittest.TestCase):
    def test_classify_lean_error_all_classes(self):
        self.assertEqual(ledger.classify_lean_error("", accepted=True), "none")
        self.assertEqual(ledger.classify_lean_error("", accepted=None), "unverified")
        self.assertEqual(
            ledger.classify_lean_error("error: unknown identifier 'Primrec.foo'", accepted=False),
            "unknown identifier",
        )
        self.assertEqual(
            ledger.classify_lean_error("error: type mismatch\n  has type Nat\n  expected Bool", accepted=False),
            "type mismatch",
        )
        self.assertEqual(
            ledger.classify_lean_error("error: unsolved goals\n⊢ Primrec f", accepted=False),
            "unsolved goals",
        )
        self.assertEqual(
            ledger.classify_lean_error("timeout after 300s", timed_out=True, accepted=False),
            "timeout",
        )
        self.assertEqual(
            ledger.classify_lean_error("error: unexpected token ':='; expected command", accepted=False),
            "syntax",
        )
        self.assertEqual(
            ledger.classify_lean_error("error: maximum recursion depth reached", accepted=False),
            "other",
        )

    def test_append_and_summarize_ledger(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lpath = root / ".agents" / "gemma_usage.jsonl"

            # T0 decl accepted at attempt 1
            ledger.append_usage_record(
                declaration="Turing.BlankExtends.refl",
                milestone="W0",
                tier="T0",
                attempt=1,
                accepted=True,
                tokens=42,
                latency_ms=1200.0,
                lean_ms=800.0,
                ledger_path=lpath,
            )
            # T1 decl fails attempt 1, succeeds attempt 2
            ledger.append_usage_record(
                declaration="Primrec.option_some",
                milestone="W0",
                tier="T1",
                attempt=1,
                accepted=False,
                compiler_output="error: unknown identifier 'foo'",
                tokens=50,
                latency_ms=1500.0,
                lean_ms=900.0,
                ledger_path=lpath,
            )
            ledger.append_usage_record(
                declaration="Primrec.option_some",
                milestone="W0",
                tier="T1",
                attempt=2,
                accepted=True,
                tokens=60,
                latency_ms=1600.0,
                lean_ms=850.0,
                ledger_path=lpath,
            )
            # T2 decl fails all 5 attempts
            for att in range(1, 6):
                ledger.append_usage_record(
                    declaration="Turing.eval_partrec",
                    milestone="M1",
                    tier="T2",
                    attempt=att,
                    accepted=False,
                    compiler_output="error: type mismatch",
                    tokens=100,
                    latency_ms=2500.0,
                    lean_ms=1100.0,
                    ledger_path=lpath,
                )

            summary = ledger.summarize_ledger(ledger_path=lpath, repo_root=root)
            self.assertEqual(summary["total_calls"], 8)
            self.assertEqual(summary["overall"]["declarations"], 3)
            self.assertEqual(summary["overall"]["pass_at_1_count"], 1)
            self.assertEqual(summary["overall"]["pass_at_5_count"], 2)

            self.assertEqual(summary["by_tier"]["T0"]["pass_at_1"], 1.0)
            self.assertEqual(summary["by_tier"]["T1"]["pass_at_1"], 0.0)
            self.assertEqual(summary["by_tier"]["T1"]["pass_at_5"], 1.0)
            self.assertEqual(summary["by_tier"]["T2"]["pass_at_5"], 0.0)

            self.assertEqual(summary["by_milestone"]["W0"]["pass_at_5_count"], 2)
            self.assertEqual(summary["by_milestone"]["M1"]["pass_at_5_count"], 0)
            self.assertEqual(summary["by_origin"]["gemma_accepted"], 2)
            self.assertEqual(summary["by_origin"]["escalated_to_frontier"], 1)


if __name__ == "__main__":
    unittest.main()
