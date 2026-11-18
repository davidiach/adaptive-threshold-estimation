from pathlib import Path
import re
import unittest

from lean_ci import changed_paths, select_jobs


class LeanRoutingTests(unittest.TestCase):
    all_jobs = {"lean-kernel", "lean-all-modules", "entropy-tail-upper", "stopping-program"}

    def test_research_and_manuscript_only(self):
        paths = {
            "research/2026-11-17-rms-constants/SharpCap.lean", "research/README.md",
            "paper/v6/main.tex", "docs/VERIFY.md", "lean/README.md", "tools/build_v6.py",
            "tools/verify_population_research.py", "tools/verify_optimal_quantile_factor.py",
        }
        self.assertEqual(select_jobs(paths), set())

    def test_shared_inputs(self):
        for path in (".github/workflows/checks.yml", "lean/ThresholdHC.lean",
                     "lean/ThresholdHC/Tier6/Full.lean", "lean/lean-toolchain",
                     "lean/lakefile.toml", "lean/lake-manifest.json", "tools/verify_tier6.py"):
            with self.subTest(path=path):
                self.assertEqual(select_jobs({path}), self.all_jobs)

    def test_job_specific_inputs(self):
        cases = {
            "tools/definition_lock.json": {"lean-all-modules"},
            "tools/verify_project_axioms.py": {"lean-all-modules", "lean-kernel", "entropy-tail-upper"},
            "tools/verify_sharp_rms.py": {"lean-kernel", "stopping-program"},
            "tools/verify_square_root_cap.py": {"stopping-program"},
            "tools/verify_large_budget_rms.py": {"lean-kernel"},
            "tools/verify_upper_constant.py": {"lean-kernel"},
            "tools/verify_upper_work.py": {"lean-kernel"},
            "tools/verify_upper_moment.py": {"lean-kernel"},
            "tools/verify_upper_mixture.py": {"lean-kernel"},
            "tools/quantile_comparison_specification_freeze.json": {"lean-kernel", "entropy-tail-upper"},
            "tools/stopping_program_lock.py": {"stopping-program"},
            "tools/verify_genie_convergence.py": {"stopping-program"},
            "tools/verify_robust_level_certificates.py": {"entropy-tail-upper"},
            "lean/ThresholdHC/HardBudget/SPECIFICATION.sha256": {"entropy-tail-upper"},
            "toolkit/threshold_toolkit/planner.py": {"lean-kernel"},
            "proposals/constants/UniformArithmetic.lean": {"lean-kernel"},
            "results/lean_best.json": {"lean-kernel"},
            "constants/grid.json": {"lean-kernel"},
            "TIER6_FROZEN.sha256": {"lean-kernel"},
        }
        for path, jobs in cases.items():
            with self.subTest(path=path):
                self.assertEqual(select_jobs({path}), jobs)
        self.assertEqual(select_jobs(set(cases)), self.all_jobs)

    def test_manual_and_new_refs_run_all_jobs(self):
        for base in ("", "0" * 40):
            self.assertEqual(select_jobs(changed_paths(base, "HEAD")), self.all_jobs)
        self.assertEqual(select_jobs(set()), set())

    def test_each_workflow_verifier_triggers_its_job(self):
        workflow = Path(".github/workflows/checks.yml").read_text(encoding="utf-8")
        for job in self.all_jobs:
            steps = workflow.split(f"\n  {job}:\n", 1)[1]
            steps = re.split(r"^  [\w-]+:$", steps, maxsplit=1, flags=re.M)[0]
            tools = set(re.findall(r"tools/[\w]+\.py", steps))
            for group in re.findall(r"for audit in ([\w ]+); do", steps):
                tools.update(f"tools/verify_{name}.py" for name in group.split())
            self.assertTrue(tools)
            for path in tools:
                with self.subTest(job=job, path=path):
                    self.assertIn(job, select_jobs({path}))
