"""Adversarial binding/runner tests; kernel examples run in the formal audit."""
import copy
from fractions import Fraction as F
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

from threshold_toolkit import deterministic_certificates as dc


class DeterministicCertificatesTests(unittest.TestCase):
    def setUp(self):
        self.request = dc.Request("sqrt", (F(2),), bits=16, log_terms=4)
        self.certificate = dc.produce(self.request)

    def test_invalid_requests(self):
        for op, vals, kwargs in [
            ("sqrt", (True,), {}), ("sqrt", (2.0,), {}), ("sqrt", (F(-1),), {}),
            ("log", (F(0),), {}), ("entropy", (F(-1),), {}), ("other", (), {}),
            ("sqrt", (), {}), ("entropy", (F(0),)*17, {}),
            ("sqrt", ("1e999999999",), {}), ("sqrt", ("1; axiom bad : False",), {}),
            ("sqrt", (F(2),), {"bits": True}), ("log", (F(2),), {"log_terms": 257}),
            ("sqrt", (2**2048,), {}),
        ]:
            with self.subTest(op=op, vals=str(vals)[:60], kwargs=kwargs):
                with self.assertRaises(dc.VerificationError):
                    dc.Request(op, vals, **kwargs)

    def test_expected_request_binding_and_precision(self):
        for req in [dc.Request("sqrt", (F(3),), bits=16, log_terms=4),
                    dc.Request("sqrt", (F(2),), bits=17, log_terms=4),
                    dc.Request("log", (F(2),), bits=16, log_terms=4)]:
            with self.assertRaisesRegex(dc.VerificationError, "expected request"):
                dc.proof_source(req, self.certificate)

    def test_structural_tampering_and_injection(self):
        for mutate in [lambda c: c.update(extra=True), lambda c: c.update(schema="other"),
                       lambda c: c["request"].update(bits=True),
                       lambda c: c["request"].update(values=[2]),
                       lambda c: c["request"].update(values=("2",)),
                       lambda c: c["output"].update(lower=False),
                       lambda c: c["output"].update(lower="3", upper="2"),
                       lambda c: c["output"].update(upper="1); axiom forged : False"),
                       lambda c: c["output"].update(upper="1/0")]:
            c = copy.deepcopy(self.certificate)
            mutate(c)
            with self.assertRaises(dc.VerificationError):
                dc.proof_source(self.request, c)

    def test_zero_entropy_and_tiny_sqrt_source(self):
        for req in (dc.Request("entropy", ()), dc.Request("entropy", (F(0), F(0))),
                    dc.Request("sqrt", (F(3, 10**100),))):
            source = dc.proof_source(req, dc.produce(req))
            self.assertIn("theorem certified_value", source)
            self.assertNotIn("native_decide", source)
            self.assertNotIn("sorry", source)
        self.assertIn("costEntropy", dc.proof_source(dc.Request("entropy", ()),
                                                    dc.produce(dc.Request("entropy", ()))))

    def test_success_requires_kernel_reports(self):
        valid = "'certified_value' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        precision = "'certified_precision' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        dc.validate_kernel_report(valid, 0, sqrt=False)
        dc.validate_kernel_report(valid+precision, 0, sqrt=True)
        for text, code, sqrt in [("", 0, False), (valid, 1, False), (valid, 0, True),
                                 (valid+precision, 0, False), (valid+valid, 0, False),
                                 (valid.replace("propext", "sorryAx"), 0, False),
                                 (valid+"warning: declaration uses `sorry`", 0, False)]:
            with self.assertRaises(dc.VerificationError):
                dc.validate_kernel_report(text, code, sqrt=sqrt)

    def test_no_success_when_kernel_unavailable_or_timed_out(self):
        for error in [FileNotFoundError(), subprocess.TimeoutExpired("lean", 1)]:
            with patch.object(dc.subprocess, "run", side_effect=error):
                with self.assertRaises(dc.VerificationError):
                    dc.verify(self.request, self.certificate, lean_dir=Path("lean"))
        run = subprocess.CompletedProcess([], 0, "", "")
        with patch.object(dc.subprocess, "run", return_value=run):
            with self.assertRaises(dc.VerificationError):
                dc.verify(self.request, self.certificate, lean_dir=Path("lean"))

    def test_limits_and_actual_producer_output(self):
        from threshold_toolkit.rare_event_functional import sqrt_interval
        self.assertEqual(self.certificate["output"], sqrt_interval(F(2), 16).as_dict())
        with patch.object(dc, "MAX_SOURCE_BYTES", 10):
            with self.assertRaisesRegex(dc.VerificationError, "source-size"):
                dc.proof_source(self.request, self.certificate)
        with self.assertRaises(dc.VerificationError):
            dc.verify(self.request, self.certificate, lean_dir=Path("lean"), timeout=float("nan"))

    def test_result_keeps_the_proved_snapshot(self):
        original = dict(self.certificate["output"])
        report = "'certified_value' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        report += "'certified_precision' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        def concurrent_mutation(*args, **kwargs):
            self.certificate["output"] = {"lower": "0", "upper": "0"}
            return subprocess.CompletedProcess([], 0, report, "")
        with patch.object(dc.subprocess, "run", side_effect=concurrent_mutation):
            checked = dc.verify(self.request, self.certificate, lean_dir=Path("lean"))
        self.assertEqual(checked["output"], original)


if __name__ == "__main__":
    unittest.main()
