import tempfile
import unittest
from pathlib import Path
import sys

TOOLS_DIR = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import index as bm25_index


class TestBM25Index(unittest.TestCase):
    def test_extract_declarations_and_exclusion(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            sample_file = root / "Sample.lean"
            sample_file.write_text(
                "namespace Turing\n\n"
                "/-- Reflexivity of BlankExtends. -/\n"
                "theorem BlankExtends.refl (l : List Nat) : l = l :=\n"
                "  rfl\n\n"
                "private theorem BlankExtends.refl' (l : List Nat) : l = l :=\n"
                "  rfl\n\n"
                "theorem BlankExtends.trans_aux (l : List Nat) : l = l :=\n"
                "  rfl\n\n"
                "theorem BlankExtends.trans (l : List Nat) : l = l :=\n"
                "  BlankExtends.trans_aux l\n\n"
                "theorem unproved_lemma (l : List Nat) : l = l := by\n"
                "  sorry\n\n"
                "end Turing\n",
                encoding="utf-8",
            )
            decls, proofs = bm25_index.extract_declarations_from_file(sample_file, root)
            names = [d["name"] for d in decls]
            # Private and sorry declarations must be excluded
            self.assertIn("Turing.BlankExtends.refl", names)
            self.assertIn("Turing.BlankExtends.trans", names)
            self.assertIn("Turing.BlankExtends.trans_aux", names)
            self.assertNotIn("Turing.BlankExtends.refl'", names)
            self.assertNotIn("Turing.unproved_lemma", names)
            self.assertEqual(len(proofs), 3)

            idx = bm25_index.InvertedBM25()
            idx.fit(decls)

            # Query without exclusion
            hits = idx.search("BlankExtends.trans List Nat", top_k=5)
            hit_names = [h["name"] for h in hits]
            self.assertIn("Turing.BlankExtends.trans", hit_names)

            # Query with --exclude BlankExtends.trans must hide both trans and trans_aux
            hits_ex = idx.search(
                "BlankExtends.trans List Nat",
                top_k=5,
                exclude=["Turing.BlankExtends.trans"],
            )
            hit_ex_names = [h["name"] for h in hits_ex]
            self.assertNotIn("Turing.BlankExtends.trans", hit_ex_names)
            self.assertNotIn("Turing.BlankExtends.trans_aux", hit_ex_names)


if __name__ == "__main__":
    unittest.main()
