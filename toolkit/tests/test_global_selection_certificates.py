import copy
from fractions import Fraction as F
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

from threshold_toolkit import global_selection_certificates as gc


class GlobalSelectionCertificatesTests(unittest.TestCase):
    def request(self, op="exhaustive", **kw):
        return gc.Request(op, ((F(1,4),F(1,2)), (F(1,2),F(1,2))), bits=16, log_terms=4, **kw)

    def test_all_producers_return_their_core_fields(self):
        for op in ("exhaustive", "dp", "approximate"):
            r = self.request(op, budget=F(1024))
            cert = gc.produce(r)
            self.assertEqual(len(cert["menu"]), cert["output"]["suffix_count"])
            self.assertEqual(gc._snapshot(r, cert), cert)
            source = gc.proof_source(r, cert)
            self.assertIn("suffix_attains", source)
            self.assertIn("complete_menu", source)
            self.assertIn("global_enclosure", source)
            self.assertIn("#print axioms certified_value", source)
            self.assertNotIn("native_decide", source)
            if op == "approximate":
                self.assertIn("relative_certificate", source)
                self.assertIn("witness_bounds", source)
            if cert["output"].get("optimality_proved"):
                self.assertIn("global_optimality", source)

    def test_saturation_preserves_missing_legacy_witness(self):
        r = self.request(budget=F(1))
        cert = gc.produce(r)
        self.assertIsNone(cert["output"]["selected"])
        self.assertEqual(cert["output"]["value"], {"lower":"1/4", "upper":"1/4"})

    def test_same_band_menu_is_suffixes_not_all_subsets(self):
        r = gc.Request("exhaustive", ((F(1,3),F(1,2)),(F(3,8),F(1,2))))
        self.assertEqual(gc._menu(r), [0,2,3])

    def test_domain_and_resource_limits(self):
        atoms = ((F(1,2),F(1)),)
        for kw in (dict(operation="other"), dict(atoms=list(atoms)), dict(rho=True), dict(budget=0),
                   dict(epsilon=0), dict(epsilon=2), dict(epsilon=0.1), dict(bits=True),
                   dict(max_work=True), dict(max_work=0), dict(max_work=4097),
                   dict(atoms=tuple((F(i,16), F(1,7)) for i in range(1,8)))):
            args = dict(operation="dp", atoms=atoms)
            args.update(kw)
            with self.subTest(kw=kw), self.assertRaises((gc.VerificationError, ValueError)):
                gc.Request(**args)

    def test_producer_limit_is_an_exception_not_partial_success(self):
        for op in ("exhaustive", "dp", "approximate"):
            with self.subTest(op=op), self.assertRaises(ValueError):
                gc.produce(self.request(op, max_work=1))

    def test_strict_schema_and_request_binding(self):
        r = self.request("dp")
        original = gc.produce(r)
        changes = [lambda c:c.update(extra=0), lambda c:c.update(schema=1),
                   lambda c:c["request"].update(bits=True),
                   lambda c:c["output"].update(extra=1),
                   lambda c:c["output"].update(selected=[0,1]),
                   lambda c:c["output"].update(selected=None),
                   lambda c:c["output"].update(suffix_count=True),
                   lambda c:c["output"].update(optimality_proved=1),
                   lambda c:c["output"]["value"].update(lower="by sorry"),
                   lambda c:c["output"]["value"].update(lower=0),
                   lambda c:c["output"]["value"].update(lower="1",upper="0"),
                   lambda c:c["output"]["value"].update(lower="1",upper="2"),
                   lambda c:c.update(menu=[True]), lambda c:c.update(menu=[-1]),
                   lambda c:c.update(menu=[4]), lambda c:c.update(menu=[])]
        for change in changes:
            cert = copy.deepcopy(original)
            change(cert)
            with self.subTest(cert=cert), self.assertRaises(gc.VerificationError):
                gc.proof_source(r, cert)

    def test_invalid_mathematical_witnesses_are_kernel_obligations(self):
        r = self.request()
        cert = gc.produce(r)
        cert["menu"] = [0]
        cert["output"]["suffix_count"] = 1
        source = gc.proof_source(r, cert)
        self.assertIn("private theorem complete_menu", source)
        self.assertIn("candidates.length = 1", source)
        cert["menu"] = [0,0]
        self.assertIn("candidates.Nodup", gc.proof_source(r, cert))

    def test_kernel_failure_and_missing_report_fail_closed(self):
        r = self.request()
        cert = gc.produce(r)
        for result in (subprocess.CompletedProcess([],1,"error: failed",""),
                       subprocess.CompletedProcess([],0,"",""),
                       subprocess.CompletedProcess([],0,"'certified_value' depends on axioms: [sorryAx]","")):
            with patch.object(gc.subprocess,"run",return_value=result), self.assertRaises(gc.VerificationError):
                gc.verify(r,cert,lean_dir=Path("lean"))
        for error in (OSError("missing"), subprocess.TimeoutExpired("lean",1)):
            with patch.object(gc.subprocess,"run",side_effect=error), self.assertRaises(gc.VerificationError):
                gc.verify(r,cert,lean_dir=Path("lean"))

    def test_returned_data_are_a_snapshot_of_the_proved_input(self):
        r = self.request("approximate")
        cert = gc.produce(r)
        original = copy.deepcopy(cert)
        def run(*args, **kw):
            cert["output"]["value"]["upper"] = "0"
            cert["menu"].clear()
            return subprocess.CompletedProcess([],0,"'certified_value' depends on axioms: [propext, Classical.choice, Quot.sound]","")
        with patch.object(gc.subprocess,"run",side_effect=run):
            result = gc.verify(r,cert,lean_dir=Path("lean"))
        self.assertEqual(result["output"],original["output"])
        self.assertEqual(result["menu"],original["menu"])
        self.assertFalse(result["python_execution_verified"])
        self.assertFalse(result["internal_solver_trace_verified"])
        self.assertFalse(result["polynomial_verification_cost_verified"])

    def test_timeout_validation(self):
        r = self.request()
        for timeout in (True,0,-1,601,float("nan")):
            with self.subTest(timeout=timeout), self.assertRaises(gc.VerificationError):
                gc.verify(r,gc.produce(r),lean_dir=Path("lean"),timeout=timeout)


if __name__ == "__main__":
    unittest.main()
