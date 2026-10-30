"""Exercise the public rare-event command and its numerical-scope reporting."""

import contextlib
import io
import json
import math
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit.__main__ import main as toolkit_main
from threshold_toolkit.rare_event_cli import main


class RareEventCommandTests(unittest.TestCase):
    def invoke(self, arguments, entry=main):
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            status = entry(arguments)
        return status, stdout.getvalue(), stderr.getvalue()

    def test_root_command_reports_analytic_single_atom_value(self):
        status, output, errors = self.invoke(
            ["rare-event", "--gaps", "0.25", "--rarity", "0.1", "--budget", "10000", "--json"],
            toolkit_main)
        self.assertEqual((status, errors), (0, ""))
        report = json.loads(output)
        # For one gap d, the quantile split has masses rho and 1-rho.
        expected = (0.1 + math.sqrt(0.1 * 0.9)) / (0.25 * 100)
        self.assertAlmostEqual(report["evaluation"]["value"], expected)
        self.assertAlmostEqual(report["evaluation"]["selection_lower"], 3 * expected / 5)
        self.assertIn("not an achieved error", report["scope"])

    def test_target_above_cap_reports_infimum_without_fake_evaluation(self):
        status, output, errors = self.invoke(
            ["--gaps", "0.25", "--rarity", "0.1", "--target-rate", "0.1", "--json"])
        self.assertEqual((status, errors), (0, ""))
        report = json.loads(output)
        self.assertEqual(report["inversion"]["status"], "saturated")
        self.assertEqual(report["inversion"]["budget"], 0)
        self.assertIsNone(report["inversion"]["log_budget"])
        self.assertIsNone(report["evaluation"])

    def test_overflow_is_explicit_and_json_has_no_nonstandard_numbers(self):
        arguments = ["--gaps", "1e-200", "--rarity", "0.01", "--target-rate", "0.001"]
        status, output, errors = self.invoke(arguments + ["--json"])
        self.assertEqual((status, errors), (0, ""))
        self.assertNotIn("Infinity", output)
        self.assertNotIn("NaN", output)
        report = json.loads(output)
        self.assertEqual(report["inversion"]["status"], "overflow")
        self.assertIsNone(report["inversion"]["budget"])
        self.assertGreater(report["inversion"]["log_budget"], math.log(sys.float_info.max))
        self.assertIsNone(report["evaluation"])
        status, output, _ = self.invoke(arguments)
        self.assertEqual(status, 0)
        self.assertIn("exceeds the floating-point range", output)
        self.assertNotIn("impossible", output)

    def test_invalid_inputs_fail_without_a_report(self):
        for arguments in (
                ["--gaps", "0", "--rarity", "0.1", "--budget", "100"],
                ["--gaps", "0.1,0.2", "--weights", "1", "--rarity", "0.1", "--budget", "100"],
                ["--gaps", "0.1", "--rarity", "nan", "--budget", "100"],
                ["--gaps", "0.1", "--rarity", "0.1", "--target-rate", "0"],
                ["--gaps", "0.1", "--rarity", "0.1", "--budget", "inf"]):
            with self.subTest(arguments=arguments):
                status, output, errors = self.invoke(arguments)
                self.assertEqual((status, output), (2, ""))
                self.assertTrue(errors.startswith("error:"))

    def test_direct_command_needs_only_standard_library(self):
        package_root = str(Path(__file__).resolve().parents[1])
        code = (f"import sys; sys.path.insert(0, {package_root!r}); "
                "from threshold_toolkit.rare_event_cli import main; "
                "raise SystemExit(main(['--gaps','0.25','--rarity','0.1','--budget','10000']))")
        result = subprocess.run([sys.executable, "-S", "-c", code],
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Q(B), capped at rho:", result.stdout)


if __name__ == "__main__":
    unittest.main()
