import tempfile
import unittest
from pathlib import Path
import sys

TOOLS_DIR = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import workflow_control


class TestWorkflowControl(unittest.TestCase):
    def test_strip_lean_comments_nested_and_line(self):
        src = (
            "-- top comment sorry\n"
            "theorem a : True := by /-\n"
            "  nested /- sorry -/ block\n"
            "-/ trivial -- inline axiom\n"
        )
        stripped = workflow_control.strip_lean_comments(src)
        self.assertNotIn("sorry", stripped)
        self.assertNotIn("axiom", stripped)
        self.assertIn("theorem a : True := by", stripped)
        self.assertIn("trivial", stripped)

    def test_contract_files_match_turing_recursive_milestones(self):
        keys = set(workflow_control.CONTRACT_FILES.keys())
        self.assertEqual(keys, {"M1", "M2a", "M2", "M3", "M4", "M5", "M6", "M7"})
        for path in workflow_control.CONTRACT_FILES.values():
            self.assertTrue(path.startswith("TuringRecursive/"))
            self.assertTrue(path.endswith(".lean"))

    def test_strip_lean_comments_preserves_strings(self):
        src = (
            'def s : String := "-- not a comment /- neither -/"\n'
            "def c : Char := '\"'\n"
            "-- real comment sorry\n"
            "theorem after_str : True := trivial\n"
        )
        stripped = workflow_control.strip_lean_comments(src)
        self.assertNotIn("real comment", stripped)
        self.assertIn("theorem after_str : True := trivial", stripped)

    def test_pause_resume_and_scan_contracts(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "TuringRecursive").mkdir()
            (root / "TuringRecursive" / "Eval.lean").write_text(
                "theorem t1 : True := trivial\n", encoding="utf-8"
            )
            (root / "TuringRecursive" / "Encoding.lean").write_text(
                "theorem t2 : True := by sorry\n", encoding="utf-8"
            )
            ctl = workflow_control.WorkflowController(root)
            self.assertFalse(ctl.is_paused())
            st = ctl.get_status()
            self.assertEqual(st["state"], "RUNNING")
            self.assertEqual(st["summary"]["present"], 2)
            self.assertEqual(st["summary"]["sorry_free"], 1)

            p = ctl.pause(reason="testing pause", unload_ollama=False)
            self.assertTrue(p["paused"])
            self.assertTrue(ctl.is_paused())

            r = ctl.resume()
            self.assertTrue(r["resumed"])
            self.assertFalse(ctl.is_paused())


if __name__ == "__main__":
    unittest.main()
