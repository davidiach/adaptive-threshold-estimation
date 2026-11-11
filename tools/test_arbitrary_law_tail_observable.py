"""Reject unregistered declarations, proof escapes and unsound reports in the tail-observable audit."""
import unittest
from unittest.mock import patch

import verify_arbitrary_law_tail_observable as audit
import verify_blind_upper_components as shared

PREFIX = "ThresholdHC.ArbitraryLawAdaptation."


def report(roots, axioms="propext, Classical.choice, Quot.sound"):
    return "".join(f"'{root}' depends on axioms: [{axioms}]\n" for root in sorted(roots))


class TailObservableAuditTests(unittest.TestCase):
    def test_every_declaration_is_restated_and_reported(self):
        source, roots = audit.audit_input()
        self.assertEqual(sorted(audit.declared_names()), sorted(audit.NAMES))
        self.assertEqual(len(set(audit.NAMES)), len(audit.NAMES))
        self.assertEqual(roots, {PREFIX + name for name in audit.NAMES})
        self.assertEqual(source.count("example "), len(audit.NAMES))
        self.assertEqual(source.count("#print axioms "), len(roots))
        shared.validate_reports(report(roots), 0, roots)

    def test_reader_is_restated_in_full(self):
        source, _ = audit.audit_input()
        # The state, its fields in order, and the step at a checkpoint.
        self.assertIn("(ProbeState.mk c l n h k b).coin = c ∧ (ProbeState.mk c l n h k b).level = l",
                      source)
        self.assertIn("probeInit M = ⟨0, 0, 0, 0, 0, decide (M = 0)⟩", source)
        self.assertIn("decide (2 * (tailThreshold J k : ℤ) < |2 * (h : ℤ) - ((4 ^ k : ℕ) : ℤ)|)",
                      source)
        self.assertIn("if J ≤ st.level ∨ probeResolved J st.level (st.heads + b.toNat) = true then",
                      source)
        self.assertIn("count := if st.stopped = true then st.count else st.count + 1", source)
        self.assertIn("stopped := st.stopped || !probeResolved J st.level (st.heads + b.toNat) ||\n"
                      "            decide (M < st.coin + 2) }", source)
        self.assertIn("probeReader J M = fun w => (probeRun J M w).coin", source)
        # Every clause of the invariant.
        self.assertIn("probeWork J s st.coin + st.len = t ∧ st.heads = tailHeads st.len (s st.coin)",
                      source)
        self.assertIn("tbl st.coin = tapeDrop st.len (s st.coin) ∧ (∀ j, st.coin < j → tbl j = s j)",
                      source)
        self.assertIn("(st.stopped = true ↔ ¬ probeAdmits J M s (st.coin + 1))", source)
        # The count from the observed word is the tape-level count, at every budget and prefix.
        self.assertIn("probeWordCompleted J M (readBlock b (probeReader J M) s).1 = "
                      "probeCompleted J b M s", source)
        self.assertIn("(s : Table) {t b : ℕ} (h : t ≤ b)", source)
        self.assertIn("t < probeWork J s (probeReader J M (readBlock t (probeReader J M) s).1 + 1)",
                      source)

    def test_blocks_and_transfer_carry_their_labels_and_hypotheses(self):
        source, _ = audit.audit_input()
        # Blocks run one after another on the coins of their own label.
        self.assertIn("thenRead (seqOffset len n) (seqReader len p n) (Nat.pair n ∘ p n)", source)
        self.assertIn("(readBlock (len n) (p n) (fun i => s (Nat.pair n i))).1) ∧", source)
        self.assertIn("medianUpper J m (fun j => min (t - j * b) b) (fun _ => M)", source)
        self.assertIn("(fun j i => s (Nat.pair J (Nat.pair j i)))", source)
        # The estimator buys exactly its block and reports a function of the observed word.
        self.assertIn("(wordEstimator n p out).policy = (fun _ => stopAt n p) ∧", source)
        self.assertIn("(wordEstimator n p out).output = fun z => out (processHistory z.2 n)", source)
        self.assertIn("PathwiseCap (tailEstimator J m b M) (m * b)", source)
        # The transfer is an equality of probabilities for every event about the word.
        self.assertIn("(S : Set (List Bool)),\n"
                      "    (experimentLaw μ (wordEstimator n p out) q).real "
                      "{z | processHistory z.2 n ∈ S} =", source)
        self.assertIn("{ω | (readBlock n p ω).1 ∈ S} := @original_word_event", source)
        # Statements (1) and (3) under the law of the original experiment, for every sign law.
        self.assertIn("(hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) "
                      "(hmδ : 8 * log (2 / δ) ≤ m)", source)
        self.assertIn("(experimentLaw μ (tailEstimator J m (4 ^ J) (4 ^ J)) q).real", source)
        self.assertIn("medianWordUpper J m (4 ^ J) (4 ^ J) ((processHistory z.2 (m * 4 ^ J)).take t))",
                      source)
        self.assertIn("(hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) "
                      "(hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J)", source)
        self.assertIn("524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)", source)
        # The depths up to L, with the union calibration.
        self.assertIn("(hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J)",
                      source)
        self.assertIn("{z | ∀ J, 1 ≤ J → J ≤ L →", source)
        self.assertIn("(TailOnset μ ρ J →", source)
        self.assertIn("(J₀ ≤ J →", source)
        self.assertIn("(q : SignLaw)", source)

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
