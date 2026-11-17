"""Execution-boundary tests; numerical acceptance is separately replayed in Lean."""
import copy
from fractions import Fraction as F
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

from threshold_toolkit import finite_law_certificates as fc


class FiniteCertificateTests(unittest.TestCase):
    def request(self, operation="objective", **kw):
        defaults = dict(atoms=((F(1, 8), F(1, 4)), (F(1, 2), F(3, 4))),
                        selected=(F(1, 2), F(1)) if operation == "objective" else (),
                        bits=16, log_terms=4)
        defaults.update(kw)
        return fc.Request(operation, **defaults)

    def test_canonical_domain(self):
        for atoms in [(), ((0, 1),), ((F(3, 4), 1),), ((F(1, 2), 0),),
                      ((F(1, 8), F(1, 3)),), ((F(1, 2), F(1, 2)), (F(1, 8), F(1, 2))),
                      ((F(1, 8), F(1, 2)), (F(1, 8), F(1, 2))), ((F(1, 2**260), 1),)]:
            with self.subTest(atoms=atoms), self.assertRaises(fc.VerificationError):
                self.request(atoms=atoms)

    def test_exact_types_and_limits(self):
        for kw in [dict(rho=True), dict(budget=1.0), dict(rho="0.25"), dict(cap=True),
                   dict(heads=-1), dict(tails=129), dict(bits=True), dict(log_terms=3),
                   dict(selected=(F(1),)), dict(selected=(F(-1), F(1))),
                   dict(rho=F(1, 2)), dict(budget=0), dict(cap=0),
                   dict(rho="1); axiom bad : False"), dict(budget=1 << 2049)]:
            with self.subTest(kw=kw), self.assertRaises(fc.VerificationError):
                self.request(**kw)
        with self.assertRaises(fc.VerificationError):
            self.request("oracle", selected=(F(0), F(1)))

    def test_actual_producer_paths(self):
        for operation in ("objective", "oracle", "prefix"):
            r = self.request(operation)
            c = fc.produce(r)
            source = fc.proof_source(r, c)
            self.assertIn("theorem certified_value", source)
            self.assertIn("IsProbabilityMeasure law", source)
            self.assertNotIn("native_decide", source)
            self.assertNotIn("sorry", source)
            self.assertEqual(c["request"], r.as_dict())
        r = self.request("prefix", atoms=((F(1, 2), F(1)),), heads=0, tails=0)
        self.assertEqual(fc.produce(r)["output"], dict(lower="1", upper="1"))

    def test_expected_request_binding(self):
        r = self.request()
        c = fc.produce(r)
        replacements = dict(rho="1/8", budget="100", bits=32, log_terms=8, cap=17,
                            heads=1, tails=1, selected=["0", "1"], operation="oracle",
                            atoms=[["1/8", "1/2"], ["1/2", "1/2"]])
        for k, v in replacements.items():
            forged = copy.deepcopy(c)
            forged["request"][k] = v
            with self.subTest(k=k), self.assertRaises(fc.VerificationError):
                fc.proof_source(r, forged)
        c["request"]["heads"] = False
        with self.assertRaises(fc.VerificationError):
            fc.proof_source(r, c)

    def test_no_output_code_or_shape_injection(self):
        r = self.request()
        for value in (True, 0.1, "0; axiom bad : False", "1/0", "9"*9000):
            c = fc.produce(r)
            c["output"]["lower"] = value
            with self.subTest(value=str(value)[:30]), self.assertRaises(fc.VerificationError):
                fc.proof_source(r, c)
        for field in ("schema", "request", "output"):
            c = fc.produce(r)
            del c[field]
            with self.assertRaises(fc.VerificationError):
                fc.proof_source(r, c)

    def test_oracle_shape_and_unknown_bands(self):
        r = self.request("oracle")
        for key, value in [("core", ["1"]), ("core", ("0", "1")),
                           ("band_costs", {999: "1"}), ("band_costs", {"999": "1"}),
                           ("threshold", "1/3"), ("tail_work", True)]:
            c = fc.produce(r)
            c["output"][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(fc.VerificationError):
                fc.proof_source(r, c)

    def test_false_claim_is_encoded_for_kernel_rejection(self):
        r = self.request()
        c = fc.produce(r)
        c["output"] = dict(lower="99", upper="99")
        source = fc.proof_source(r, c)
        self.assertIn("(99/1:ℚ)", source)
        self.assertIn("selection_upper", source)
        self.assertIn("selectionObjective law", source)

    def test_fail_closed_without_kernel(self):
        r = self.request()
        for exc in (OSError(), subprocess.TimeoutExpired("lean", 1)):
            with patch.object(fc.subprocess, "run", side_effect=exc), self.assertRaises(fc.VerificationError):
                fc.verify(r, fc.produce(r), lean_dir=Path("lean"))
        for report, code in [("", 0), ("'certified_value' depends on axioms: [sorryAx]", 0),
                             ("'certified_value' depends on axioms: [propext]", 1)]:
            run = subprocess.CompletedProcess([], code, report, "")
            with patch.object(fc.subprocess, "run", return_value=run), self.assertRaises(fc.VerificationError):
                fc.verify(r, fc.produce(r), lean_dir=Path("lean"))

    def test_snapshot_survives_caller_mutation(self):
        r = self.request()
        c = fc.produce(r)
        original = copy.deepcopy(c["output"])
        def run(*args, **kw):
            c["output"]["upper"] = "0"
            return subprocess.CompletedProcess([], 0, "'certified_value' depends on axioms: [propext, Classical.choice, Quot.sound]", "")
        with patch.object(fc.subprocess, "run", side_effect=run):
            checked = fc.verify(r, c, lean_dir=Path("lean"))
        self.assertEqual(checked["output"], original)
        self.assertFalse(checked["global_optimum_verified"])

    def test_timeout_and_source_limits(self):
        r = self.request()
        for timeout in (True, 0, 601, float("nan")):
            with self.assertRaises(fc.VerificationError):
                fc.verify(r, fc.produce(r), lean_dir=Path("lean"), timeout=timeout)
        with patch.object(fc.dc, "MAX_SOURCE_BYTES", 10), self.assertRaises(fc.VerificationError):
            fc.proof_source(r, fc.produce(r))


if __name__ == "__main__":
    unittest.main()
