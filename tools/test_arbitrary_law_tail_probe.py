"""Reject unregistered declarations, proof escapes and unsound reports in the tail-probe audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_tail_probe as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class TailProbeAuditTests(unittest.TestCase):
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
        # The stopping rule, the completed count, the charge and the certificate.
        self.assertIn("n ≤ M ∧ ∀ i, i + 1 < n → ¬ tailUnresolved J (ω i)", source)
        self.assertIn("probeAdmits J M ω n ∧ probeWork J ω n ≤ b", source)
        self.assertIn("probeCompleted J b M ω = sSup {n | probeReaches J b M ω n}", source)
        self.assertIn("probeFlips J b M ω = min b (probeWork J ω (probeHorizon J M ω))", source)
        self.assertIn("if n = 0 then (1 : ℝ) else min 1 (8 / (n : ℝ))", source)
        # An interrupted coin is charged and is not counted.
        self.assertIn(
            "probeFlips J b M ω = b ∧ b < probeWork J ω (probeCompleted J b M ω + 1)", source)
        # Validity is simultaneous in the budget and the coin cap, at level 7/8.
        self.assertIn("(hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t})", source)
        self.assertIn("7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))"
                      ".real\n      {ω | ∀ b M, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤",
                      source)
        # Performance at a fixed positive budget and coin cap, at level 3/4.
        self.assertIn("(hb : 0 < b) (hM : 0 < M)", source)
        self.assertIn("(hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W)", source)
        self.assertIn("min 1 (128 * max (max (tailUnresolvedMass μ J)", source)
        self.assertIn("((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))", source)
        self.assertIn("(hb : 0 < b) (hbM : b ≤ M)", source)
        # The statements hold for every sign law, on the coin array of the experiment.
        self.assertIn("(q : SignLaw)", source)
        self.assertIn("(originalSimulationLaw μ A q).map Prod.snd =", source)

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
            shared.validate_reports(report(roots), 1, roots)


if __name__ == "__main__":
    unittest.main()
