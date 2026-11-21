import os
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


class TestAuditAxiomsAndWiring(unittest.TestCase):
    def test_token_scan_ignores_comments_and_catches_code_tokens(self):
        script = REPO_ROOT / "tools" / "collect_axioms.sh"
        with tempfile.TemporaryDirectory() as td:
            clean_file = Path(td) / "Clean.lean"
            clean_file.write_text(
                "-- comment with sorry and axiom\n"
                "/- block comment with native_decide and maxHeartbeats -/\n"
                "theorem clean_thm : True := trivial\n",
                encoding="utf-8",
            )
            r_clean = subprocess.run(
                ["bash", str(script), "--scan-only", str(clean_file)],
                capture_output=True,
                text=True,
            )
            self.assertEqual(r_clean.returncode, 0, r_clean.stderr)

            dirty_file = Path(td) / "Dirty.lean"
            dirty_file.write_text(
                "theorem dirty_thm : True := by sorry\n",
                encoding="utf-8",
            )
            r_dirty = subprocess.run(
                ["bash", str(script), "--scan-only", str(dirty_file)],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(r_dirty.returncode, 0)
            self.assertIn("sorry", r_dirty.stderr)

    def test_audit_wiring_passes_real_use_and_fails_decorative_have(self):
        env = os.environ.copy()
        elan_bin = os.path.expanduser("~/.elan/bin")
        env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
        env["LEAN_NUM_THREADS"] = "2"

        audit_src = (REPO_ROOT / "tools" / "audit_axioms.lean").read_text(encoding="utf-8")

        with tempfile.TemporaryDirectory() as td:
            # 1. Genuine dependency passes #audit_wiring
            pass_file = Path(td) / "WiringPass.lean"
            pass_file.write_text(
                audit_src
                + "\nlemma req_helper (n : Nat) : n = n := rfl\n"
                + "theorem genuine_consumer (n : Nat) : n = n := req_helper n\n"
                + "#audit_wiring genuine_consumer [req_helper]\n",
                encoding="utf-8",
            )
            p1 = subprocess.run(
                ["lake", "env", "lean", str(pass_file)],
                cwd=str(REPO_ROOT),
                env=env,
                capture_output=True,
                text=True,
                timeout=60,
            )
            self.assertEqual(p1.returncode, 0, f"Expected pass, got:\n{p1.stdout}\n{p1.stderr}")

            # 2. Decorative `have` fails #audit_wiring
            fail_file = Path(td) / "WiringDecorativeFail.lean"
            fail_file.write_text(
                audit_src
                + "\nlemma req_helper (n : Nat) : n = n := rfl\n"
                + "theorem decorative_consumer (n : Nat) : n = n := by\n"
                + "  have _unused := req_helper n\n"
                + "  rfl\n"
                + "#audit_wiring decorative_consumer [req_helper]\n",
                encoding="utf-8",
            )
            p2 = subprocess.run(
                ["lake", "env", "lean", str(fail_file)],
                cwd=str(REPO_ROOT),
                env=env,
                capture_output=True,
                text=True,
                timeout=60,
            )
            self.assertNotEqual(p2.returncode, 0, "Expected decorative `have` to fail #audit_wiring")
            combined_out = (p2.stdout or "") + "\n" + (p2.stderr or "")
            self.assertIn("#audit_wiring FAILED", combined_out)


if __name__ == "__main__":
    unittest.main()
