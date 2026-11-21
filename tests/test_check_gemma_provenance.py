import json
import tempfile
import unittest
from pathlib import Path
import sys

TOOLS_DIR = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import check_gemma_provenance


class TestCheckGemmaProvenance(unittest.TestCase):
    def test_find_new_declarations_and_verify_provenance(self):
        old_text = (
            "namespace TuringRecursive\n"
            "theorem existing_thm : True := trivial\n"
            "end TuringRecursive\n"
        )
        new_text = (
            "namespace TuringRecursive\n"
            "theorem existing_thm : True := trivial\n\n"
            "-- tier: T0\n"
            "theorem new_t0_thm : True := trivial\n\n"
            "theorem new_primrec_inferred (f : Nat → Nat) : Primrec f := sorry\n\n"
            "-- tier: T2\n"
            "theorem new_t2_core : True := trivial\n"
            "end TuringRecursive\n"
        )
        added = check_gemma_provenance.find_new_declarations_between_texts(old_text, new_text)
        by_name = {d.name: (d, tier) for d, tier in added}
        self.assertEqual(len(by_name), 3)
        self.assertEqual(by_name["TuringRecursive.new_t0_thm"][1], "T0")
        self.assertEqual(by_name["TuringRecursive.new_primrec_inferred"][1], "T1")
        self.assertEqual(by_name["TuringRecursive.new_t2_core"][1], "T2")

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            acc_dir = root / ".agents" / "gemma_accepted"
            esc_dir = root / ".agents" / "gemma_escalations"
            acc_dir.mkdir(parents=True)
            esc_dir.mkdir(parents=True)

            d_t0, _ = by_name["TuringRecursive.new_t0_thm"]
            d_t1, _ = by_name["TuringRecursive.new_primrec_inferred"]

            # Initially both fail provenance
            r0 = check_gemma_provenance.check_declaration_provenance(d_t0, "T0", acc_dir, esc_dir)
            self.assertFalse(r0["ok"])

            # Add accepted file for d_t0
            (acc_dir / "TuringRecursive.new_t0_thm.lean").write_text(
                "theorem new_t0_thm : True := trivial\n", encoding="utf-8"
            )
            r0_ok = check_gemma_provenance.check_declaration_provenance(d_t0, "T0", acc_dir, esc_dir)
            self.assertTrue(r0_ok["ok"])
            self.assertEqual(r0_ok["origin"], "gemma_accepted")

            # Add escalation file with only 3 attempts for d_t1 -> must fail
            esc_file = esc_dir / "TuringRecursive.new_primrec_inferred.json"
            esc_file.write_text(
                json.dumps({
                    "declaration": "TuringRecursive.new_primrec_inferred",
                    "attempts": [{"attempt": i, "accepted": False} for i in range(1, 4)],
                }),
                encoding="utf-8",
            )
            r1_short = check_gemma_provenance.check_declaration_provenance(d_t1, "T1", acc_dir, esc_dir)
            self.assertFalse(r1_short["ok"])

            # Update escalation file to 5 failed attempts -> must pass
            esc_file.write_text(
                json.dumps({
                    "declaration": "TuringRecursive.new_primrec_inferred",
                    "attempts": [{"attempt": i, "accepted": False} for i in range(1, 6)],
                }),
                encoding="utf-8",
            )
            r1_ok = check_gemma_provenance.check_declaration_provenance(d_t1, "T1", acc_dir, esc_dir)
            self.assertTrue(r1_ok["ok"])
            self.assertEqual(r1_ok["origin"], "escalated")


if __name__ == "__main__":
    unittest.main()
