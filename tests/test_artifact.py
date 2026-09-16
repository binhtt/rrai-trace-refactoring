import importlib.util
import pathlib
import sys
import unittest


MODULE_PATH = pathlib.Path(__file__).parents[1] / "src" / "rrai_refactoring.py"
SPEC = importlib.util.spec_from_file_location("rrai_refactoring", MODULE_PATH)
artifact = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = artifact
SPEC.loader.exec_module(artifact)


class ArtifactTests(unittest.TestCase):
    def test_internal_semantic_checks(self):
        artifact.run_self_tests()

    def test_complete_domain_size(self):
        self.assertEqual(len(artifact.FULL_DOMAIN), 196_608)

    def test_proof_obligation_controls(self):
        results = artifact.proof_obligations()
        valid = [
            "Priority adjustment",
            "Merging",
            "Decomposition",
            "Elimination",
        ]
        invalid = [
            "Invalid merge",
            "Invalid priority adjustment",
            "Unsafe decomposition",
        ]
        self.assertTrue(all(results[name].passed for name in valid))
        self.assertTrue(all(not results[name].passed for name in invalid))
        self.assertTrue(all(results[name].counterexample is not None for name in invalid))


if __name__ == "__main__":
    unittest.main()
