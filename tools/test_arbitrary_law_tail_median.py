"""Reject unregistered declarations, proof escapes and unsound reports in the tail-median audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_tail_median as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class TailMedianAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_statements_carry_their_constants_and_hypotheses(self):
        source, _ = audit.audit_input()
        # The median is the entry of rank floor(m/2), and 1 for no probe.
        self.assertIn("⟨m / 2, Nat.div_lt_self h (by norm_num)⟩)\n    else 1", source)
        self.assertIn("blockMedian m (fun j => probeUpper (probeCompleted J (b j) (M j) (ω j)))",
                      source)
        # Majority transfer in both directions, with strict majorities.
        self.assertIn("(h : m < 2 * blockCount m (fun j => v j ≤ c))", source)
        self.assertIn("(h : m < 2 * blockCount m (fun j => a ≤ v j))", source)
        # Hoeffding across blocks: level 1/4 for failure, 3/4 for success, rate exp(-m/8).
        self.assertIn("(hp : S.real B ≤ 1 / 4) {m : ℕ} (hm : 0 < m)", source)
        self.assertIn("(hp : 3 / 4 ≤ S.real G) {m : ℕ} (hm : 0 < m)", source)
        self.assertIn("≤ exp (-(m : ℝ) / 8)", source)
        self.assertIn("2 * exp (-(m : ℝ) / 8)", source)
        # The calibration of the number of probes and of the depth allowances.
        self.assertIn("(hδ : 0 < δ) {m : ℕ} (hm : 8 * log (2 / δ) ≤ m)", source)
        self.assertIn("δ / ((J : ℝ) * (J + 1))", source)
        self.assertIn("(hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J)",
                      source)
        # Statement (1): coverage for every choice of budgets, and the bound at budget 4^J.
        self.assertIn("(∀ b' M' : ℕ → ℕ,\n      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ "
                      "medianUpper J m b' M' ω) ∧", source)
        self.assertIn("medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) ω ≤", source)
        self.assertIn("min 1 (128 * max (tailUnresolvedMass μ J)", source)
        self.assertIn("((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))}", source)
        # The pathwise cap and the single coin array.
        self.assertIn("medianFlips J m (fun _ => b) M ω ≤ m * b", source)
        self.assertIn("(fun j i => ω (Nat.pair j i))", source)
        self.assertIn("(fun j i => ω (Nat.pair J (Nat.pair j i)))", source)
        self.assertIn("(q : SignLaw)", source)

    def test_classical_opening_is_scoped(self):
        # A file-wide opening would print the axiom as `choice` and hide its full name.
        source, _ = audit.audit_input()
        self.assertNotIn("\nopen Classical\n", source)
        self.assertEqual(source.count("open Classical in\n"), 4)

    def test_unregistered_declaration_rejected(self):
        with patch.object(audit, "declared_names", return_value=audit.NAMES + ["extra_lemma"]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()
        with patch.object(audit, "declared_names", return_value=audit.NAMES[1:]):
            with self.assertRaisesRegex(ValueError, "Unregistered or missing"):
                audit.audit_input()

    def test_proof_escape_rejected(self):
        escaped = lambda source: source + "\ntheorem hidden : False := by sorry\n"
        with patch.object(audit, "strip_comments", side_effect=escaped):
            with self.assertRaisesRegex(ValueError, "Forbidden proof escape"):
                audit.declared_names()

    def test_missing_or_unsound_report_rejected(self):
        _, roots = audit.audit_input()
        missing = sorted(roots)[1:]
        with self.assertRaises(ValueError):
            shared.validate_reports(report(missing), 0, roots)
        with self.assertRaises(ValueError):
            shared.validate_reports(report(roots, "propext, sorryAx"), 0, roots)
        with self.assertRaises(ValueError):
            shared.validate_reports(report(roots, "propext, choice, Quot.sound"), 0, roots)
        with self.assertRaises(ValueError):
            shared.validate_reports(report(roots), 1, roots)


if __name__ == "__main__":
    unittest.main()
