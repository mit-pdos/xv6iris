import importlib.util
import tempfile
import unittest
from pathlib import Path


PROFILE_PATH = Path(__file__).resolve().parents[1] / "proof_profile.py"
SPEC = importlib.util.spec_from_file_location("proof_profile", PROFILE_PATH)
profile = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(profile)


class ProofProfileTests(unittest.TestCase):
    def test_chain_annotation_uses_consumer_to_previous_dependency(self):
        chain = ["Base", "Middle", "Top"]
        annotations = {
            ("Middle", "Base"): "weak — 2.0% (1/50)",
            ("Top", "Middle"): "not weak — 40.0% (20/50)",
        }
        self.assertEqual(
            profile.chain_edge_annotation(chain, 0, annotations),
            "— (chain root)",
        )
        self.assertEqual(
            profile.chain_edge_annotation(chain, 1, annotations),
            "weak — 2.0% (1/50)",
        )
        self.assertEqual(
            profile.chain_edge_annotation(chain, 2, annotations),
            "not weak — 40.0% (20/50)",
        )

    def test_missing_analyzer_degrades_to_note(self):
        with tempfile.TemporaryDirectory() as directory:
            annotations, note = profile.load_weak_import_annotations(directory)
        self.assertEqual(annotations, {})
        self.assertIn("was not found", note)


if __name__ == "__main__":
    unittest.main()
