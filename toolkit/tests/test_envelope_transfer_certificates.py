"""Certificate boundary tests; actual numerical proofs run in the focused audit."""
import copy
from fractions import Fraction as F
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

from threshold_toolkit import envelope_transfer_certificates as ec


class EnvelopeTransferTests(unittest.TestCase):
    def envelope(self, **kw):
        return ec.EnvelopeRequest(kw.pop("cdf", (F(1), F(1, 2), F(1, 8))),
                                  bits=16, log_terms=4, **kw)

    def rounding(self, **kw):
        return ec.RoundingRequest(((F(1, 3), F(1, 2)), (F(3, 8), F(1, 2))), **kw)

    def requests(self):
        return [self.envelope(), self.envelope(cdf=(F(1),)), self.rounding(),
                ec.TransferRequest(F(1, 32), F(1, 16), F(3, 2), F(1, 128))]

    def test_envelope_domain(self):
        for cdf in [(), [1], (F(1, 2),), (1, -1), (1, 0, 1), (1, 2), (1,) * 18,
                    (True,), (1.0,), ("1; axiom bad : False",)]:
            with self.subTest(cdf=cdf), self.assertRaises(ec.VerificationError):
                self.envelope(cdf=cdf)
        for kw in [dict(rho=0), dict(rho=F(1, 2)), dict(budget=0), dict(cap=True),
                   dict(heads=-1), dict(tails=129), dict(budget=1 << 2049)]:
            with self.subTest(kw=kw), self.assertRaises(ec.VerificationError):
                self.envelope(**kw)
        for kw in [dict(bits=True), dict(bits=15), dict(log_terms=3)]:
            with self.assertRaises(ec.VerificationError):
                ec.EnvelopeRequest((F(1),), **kw)

    def test_rounding_and_transfer_domain(self):
        for subdivisions in (True, 0, 10**6 + 1, 1.0):
            with self.assertRaises(ec.VerificationError):
                self.rounding(subdivisions=subdivisions)
        for atoms in ((), ((0, 1),), ((F(1, 2), F(1, 2)),),
                      ((F(1, 2), F(1, 2)), (F(1, 8), F(1, 2)))):
            with self.assertRaises(ec.VerificationError):
                ec.RoundingRequest(atoms)
        for kw in [dict(lower=-1), dict(lower=2), dict(upper=-1), dict(rounding_factor=0),
                   dict(tv_radius=-1), dict(tv_radius=2), dict(rho=0), dict(budget=0),
                   dict(lower=True), dict(upper=0.5), dict(upper="0.5")]:
            args = dict(lower=0, upper=1)
            args.update(kw)
            with self.subTest(kw=kw), self.assertRaises(ec.VerificationError):
                ec.TransferRequest(**args)
        with self.assertRaises(ec.VerificationError):
            ec.produce(ec.TransferRequest(F(1), F(2)))

    def test_actual_outputs_and_fallback_scope(self):
        for r in self.requests():
            cert = ec.produce(r)
            source = ec.proof_source(r, cert)
            self.assertEqual(cert["request"], r.as_dict())
            self.assertIn("theorem certified_value", source)
            self.assertNotIn("native_decide", source)
            self.assertNotIn("sorry", source)
        r = self.envelope(cdf=(F(1), F(1, 4)), heads=2, tails=1)
        cert = ec.produce(r)
        self.assertEqual(cert["output"]["mode"], "fallback")
        source = ec.proof_source(r, cert)
        self.assertIn("zeroSelection law", source)
        self.assertNotIn("tailWorkIntegral tail", source)
        self.assertNotIn("private noncomputable def core", source)
        self.assertEqual(ec.produce(self.envelope(cdf=(F(1),)))["output"]["atoms"], [])

    def test_active_and_conditional_semantics(self):
        r = self.envelope()
        source = ec.proof_source(r, ec.produce(r))
        for target in ("zeroAtomLaw", "conditionalRarity", "quantileThreshold", "tailWorkIntegral",
                       "envelopeLaw_dominates", "extended_integral"):
            self.assertIn(target, source)
        r = self.requests()[-1]
        source = ec.proof_source(r, ec.produce(r))
        for premise in ("tvDist μ μ₀/2", "Measurable T", "IsProbabilityMeasure μ",
                        "Contains", "selection (μ₀.map T)", "transfer_original"):
            self.assertIn(premise, source)

    def test_duplicate_rounding_destinations(self):
        r = self.rounding(subdivisions=1)
        cert = ec.produce(r)
        self.assertEqual(cert["output"]["atoms"], [["1/2", "1"]])
        self.assertEqual(cert["output"]["destinations"], ["1/2", "1/2"])
        self.assertIn("atomic_group", ec.proof_source(r, cert))

    def test_request_binding(self):
        for r in self.requests():
            for key, value in r.as_dict().items():
                cert = ec.produce(r)
                cert["request"][key] = None
                with self.subTest(request=type(r).__name__, key=key), self.assertRaises(ec.VerificationError):
                    ec.proof_source(r, cert)
            cert = ec.produce(r)
            cert["request"]["extra"] = "0"
            with self.assertRaises(ec.VerificationError):
                ec.proof_source(r, cert)
        r = self.envelope(heads=0)
        cert = ec.produce(r)
        cert["request"]["heads"] = False
        with self.assertRaises(ec.VerificationError):
            ec.proof_source(r, cert)

    def test_injection_and_shapes(self):
        r = self.envelope()
        for value in (True, 0.1, "0; axiom bad : False", "1/0", "9" * 9000):
            cert = ec.produce(r)
            cert["output"]["zero_mass"] = value
            with self.assertRaises(ec.VerificationError):
                ec.proof_source(r, cert)
        for key, value in [("atoms", [["1/8", "1"], ["1/8", "1"]]),
                           ("atoms", [["0", "1"]]), ("core", ["0"]),
                           ("band_costs", {999: "1"}), ("band_costs", {"999": "1"}),
                           ("mode", "unknown"), ("normalized", []), ("threshold", "1/3"),
                           ("tail_work", "-1"), ("prefix", {"lower": "2", "upper": "1"})]:
            cert = ec.produce(r)
            cert["output"][key] = value
            with self.subTest(key=key), self.assertRaises(ec.VerificationError):
                ec.proof_source(r, cert)
        for field in ("schema", "request", "output"):
            cert = ec.produce(r)
            del cert[field]
            with self.assertRaises(ec.VerificationError):
                ec.proof_source(r, cert)

    def test_fallback_shape_and_rounding_support(self):
        r = self.envelope(cdf=(F(1),))
        for key, value in [("core", ["1"]), ("threshold", "1/2"),
                           ("conditional_rho", "1/4"), ("band_costs", {"0": "0"})]:
            cert = ec.produce(r)
            cert["output"][key] = value
            with self.assertRaises(ec.VerificationError):
                ec.proof_source(r, cert)
        r = self.rounding()
        for key, value in [("atoms", []), ("destinations", []), ("destinations", ["1/8", "1/8"])]:
            cert = ec.produce(r)
            cert["output"][key] = value
            with self.assertRaises(ec.VerificationError):
                ec.proof_source(r, cert)

    def test_numerical_claims_reach_kernel(self):
        for r, key in [(self.envelope(), "unresolved_mass"), (self.rounding(), "factor"),
                       (self.requests()[-1], "lower")]:
            cert = ec.produce(r)
            cert["output"][key] = "0"
            self.assertIn("theorem certified_value", ec.proof_source(r, cert))

    def test_kernel_required(self):
        r = self.requests()[-1]
        for exc in (OSError(), subprocess.TimeoutExpired("lean", 1)):
            with patch.object(ec.subprocess, "run", side_effect=exc), self.assertRaises(ec.VerificationError):
                ec.verify(r, ec.produce(r), lean_dir=Path("lean"))
        for report, code in [("", 0), ("'certified_value' depends on axioms: [sorryAx]", 0),
                             ("'certified_value' depends on axioms: [propext]", 1)]:
            run = subprocess.CompletedProcess([], code, report, "")
            with patch.object(ec.subprocess, "run", return_value=run), self.assertRaises(ec.VerificationError):
                ec.verify(r, ec.produce(r), lean_dir=Path("lean"))

    def test_snapshot_and_scope(self):
        for r in self.requests():
            cert = ec.produce(r)
            original = copy.deepcopy(cert["output"])
            def run(*args, **kw):
                cert["output"].clear()
                return subprocess.CompletedProcess([], 0,
                    "'certified_value' depends on axioms: [propext, Classical.choice, Quot.sound]", "")
            with patch.object(ec.subprocess, "run", side_effect=run):
                checked = ec.verify(r, cert, lean_dir=Path("lean"))
            self.assertEqual(checked["output"], original)
            self.assertFalse(checked["transfer_premises_verified"])
            self.assertFalse(checked["python_execution_verified"])

    def test_resource_limits(self):
        r = self.requests()[-1]
        for timeout in (True, 0, 601, float("nan")):
            with self.assertRaises(ec.VerificationError):
                ec.verify(r, ec.produce(r), lean_dir=Path("lean"), timeout=timeout)
        with patch.object(ec.dc, "MAX_SOURCE_BYTES", 10), self.assertRaises(ec.VerificationError):
            ec.proof_source(r, ec.produce(r))


if __name__ == "__main__":
    unittest.main()
