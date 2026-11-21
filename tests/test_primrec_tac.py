import os
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


class TestPrimrecTac(unittest.TestCase):
    def test_primrec_tac_closes_routine_goals(self):
        env = os.environ.copy()
        elan_bin = os.path.expanduser("~/.elan/bin")
        env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
        env["LEAN_NUM_THREADS"] = "2"

        with tempfile.TemporaryDirectory() as td:
            test_lean = Path(td) / "PrimrecTacCheck.lean"
            test_lean.write_text(
                "import TuringRecursive.Tactic.PrimrecTac\n\n"
                "open TuringRecursive.Tactic\n\n"
                "variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]\n\n"
                "theorem test_pair_swap : Primrec (fun p : α × β => (p.2, p.1)) := by\n"
                "  primrec_tac\n\n"
                "theorem test_list_cons_rev (a : α) :\n"
                "    Primrec (fun l : List α => (a :: l.reverse).tail) := by\n"
                "  primrec_tac\n\n"
                "theorem test_option_cases (f : α → Option β) (g : α → σ) (h : α → β → σ)\n"
                "    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :\n"
                "    @Primrec _ σ _ _ (fun x => Option.casesOn (f x) (g x) (h x)) := by\n"
                "  primrec_tac\n\n"
                "theorem test_computable_pair (f : α → β) (hf : Computable f) :\n"
                "    Computable (fun x : α => (f x, some x)) := by\n"
                "  primrec_tac\n",
                encoding="utf-8",
            )
            proc = subprocess.run(
                ["lake", "env", "lean", str(test_lean)],
                cwd=str(REPO_ROOT),
                env=env,
                capture_output=True,
                text=True,
                timeout=60,
            )
            self.assertEqual(
                proc.returncode,
                0,
                f"primrec_tac test failed:\n{proc.stdout}\n{proc.stderr}",
            )


if __name__ == "__main__":
    unittest.main()
