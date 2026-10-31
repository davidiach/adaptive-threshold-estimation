"""Coverage, fail-closed exact assertions and dependency scheduling regressions."""
from pathlib import Path
import unittest
from unittest.mock import patch
import verify_rare_event_completion as audit
import verify_genie_counterexample


class CompletionAuditTests(unittest.TestCase):
    def test_full_registry(self):
        ordered, paths, roots, source, _ = audit.collect()
        self.assertTrue(set(paths) <= set(ordered))
        self.assertIn("ThresholdHC.EntropyTailExecution.entropy_tail_upper", roots)
        self.assertIn("ThresholdHC.EntropyTailBridge.canonical_entropy_tail_upper", roots)
        self.assertIn("ThresholdHC.Genie.infinite_divergence_counterexample", roots)
        self.assertIn("ThresholdHC.Genie.atomConicValue_eq_genieSquared", roots)
        self.assertGreater(source.count("example :"), 90)
        self.assertEqual(source.count("#print axioms "), len(roots))
        audit.local_dependencies(ordered)

    def test_exact_escape_rejected(self):
        with patch.object(verify_genie_counterexample, "EXACT", "example : False := by sorry"):
            with self.assertRaisesRegex(ValueError,"Forbidden exact|unsafe exact"):
                audit.collect()

    def test_dependency_must_complete(self):
        a,b,c = map(Path,["A","B","C"])
        graph = {a:set(),b:{a},c:set()}
        self.assertEqual(audit.ready_paths([a,b,c],set(),graph),[a,c])
        self.assertEqual(audit.ready_paths([b,c],{a},graph),[b,c])

    def test_missing_dependency_rejected(self):
        with patch.object(Path,"read_text",return_value="import ThresholdHC.Absent\n"):
            with self.assertRaisesRegex(ValueError,"Incomplete local dependency"):
                audit.local_dependencies([Path("Test.lean")])

    def test_port_rebuild_includes_transitive_dependents(self):
        a,b,c,d = map(Path,["EntropyTailQuantile/A.lean","Runtime/B.lean","Runtime/C.lean","Other/D.lean"])
        graph = {a:set(),b:{a},c:{b},d:set()}
        self.assertEqual(audit.port_dependents([a,b,c,d],graph),{a,b,c})


if __name__ == "__main__":
    unittest.main()
