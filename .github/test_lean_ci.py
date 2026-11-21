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
            "tools/verify_pilot_feedback.py": {"lean-kernel"},
            "tools/verify_explicit_constants.py": {"lean-kernel"},
            "tools/verify_nonnegative_unbiased.py": {"lean-kernel"},
            "tools/verify_upper_constant.py": {"lean-kernel"},
            "tools/verify_upper_work.py": {"lean-kernel"},
            "tools/verify_upper_moment.py": {"lean-kernel"},
            "tools/verify_upper_mixture.py": {"lean-kernel"},
            "tools/verify_upper_cost.py": {"lean-kernel"},
            "tools/verify_upper_disagreement.py": {"lean-kernel"},
            "tools/verify_upper_sign.py": {"lean-kernel"},
            "tools/verify_upper_quarter.py": {"lean-kernel"},
            "tools/verify_upper_scale.py": {"lean-kernel"},
            "tools/verify_critical_window.py": {"entropy-tail-upper"},
            "tools/verify_paper_corollaries.py": {"entropy-tail-upper"},
            "tools/verify_paper_statements.py": {"entropy-tail-upper"},
            "tools/verify_finite_gap_corollaries.py": {"entropy-tail-upper"},
            "tools/verify_stopped_time_uniform.py": {"entropy-tail-upper"},
            "tools/verify_latent_threshold.py": {"entropy-tail-upper"},
            "tools/verify_zero_atom_split.py": {"entropy-tail-upper"},
            "tools/verify_critical_pair_rms.py": {"entropy-tail-upper"},
            "tools/verify_bias_subtraction.py": {"entropy-tail-upper"},
            "tools/verify_global_cut.py": {"entropy-tail-upper"},
            "tools/verify_psi_null.py": {"entropy-tail-upper"},
            "tools/verify_confidence_transfer_steps.py": {"entropy-tail-upper"},
            "tools/verify_observed_hoeffding.py": {"entropy-tail-upper"},
            "tools/verify_nested_assumptions.py": {"entropy-tail-upper"},
            "tools/verify_light_contraction_constant.py": {"entropy-tail-upper"},
            "tools/verify_band_cost_example.py": {"entropy-tail-upper"},
            "tools/verify_repeated_check.py": {"entropy-tail-upper"},
            "tools/verify_reservoir_termination.py": {"entropy-tail-upper"},
            "tools/verify_quantile_factor_upper.py": {"entropy-tail-upper"},
            "tools/verify_creation_charge.py": {"entropy-tail-upper"},
            "tools/verify_stage_pilot_law.py": {"entropy-tail-upper"},
            "tools/verify_bias_audit.py": {"entropy-tail-upper"},
            "tools/verify_unknown_rarity.py": {"entropy-tail-upper"},
            "tools/verify_hard_cap_necessity.py": {"entropy-tail-upper"},
            "tools/verify_pilot_correction.py": {"entropy-tail-upper"},
            "tools/verify_depth_obstruction.py": {"entropy-tail-upper"},
            "tools/verify_localization_counter.py": {"entropy-tail-upper"},
            "tools/verify_affine_comparison.py": {"entropy-tail-upper"},
            "tools/verify_two_flip_feedback.py": {"entropy-tail-upper"},
            "tools/verify_unknown_law_confidence.py": {"entropy-tail-upper"},
            "tools/verify_upper_twelve_numerics.py": {"entropy-tail-upper"},
            "tools/verify_radial_upper.py": {"entropy-tail-upper"},
            "tools/verify_time_uniform_two_sided.py": {"entropy-tail-upper"},
            "tools/verify_depth_legendre.py": {"entropy-tail-upper"},
            "tools/verify_latent_disintegration.py": {"entropy-tail-upper"},
            "tools/verify_known_gap_rarity.py": {"entropy-tail-upper"},
            "tools/verify_margin_classes.py": {"entropy-tail-upper"},
            "tools/verify_power_quantile_rows.py": {"entropy-tail-upper"},
            "tools/verify_weighted_sign_sharp.py": {"entropy-tail-upper"},
            "tools/verify_full_null_bank.py": {"entropy-tail-upper"},
            "tools/verify_robust_continuation_forms.py": {"entropy-tail-upper"},
            "tools/verify_entropy_tail_assembly.py": {"entropy-tail-upper"},
            "tools/verify_entropy_tail_forms.py": {"entropy-tail-upper"},
            "tools/verify_noninterval_selection.py": {"entropy-tail-upper"},
            "tools/verify_fixed_plan.py": {"entropy-tail-upper"},
            "tools/verify_clipping_boundary.py": {"entropy-tail-upper"},
            "tools/verify_restricted_rms.py": {"lean-kernel"},
            "tools/verify_sharp_strict.py": {"lean-kernel"},
            "tools/verify_oracle_sharpness.py": {"lean-kernel"},
            "tools/verify_oracle_upper.py": {"lean-kernel"},
            "tools/verify_clipped_output.py": {"lean-kernel"},
            "tools/verify_revisit_upper.py": {"lean-kernel"},
            "tools/verify_cap_identification_estimate.py": {"stopping-program"},
            "tools/verify_program_factor.py": {"stopping-program"},
            "tools/verify_stopping_update.py": {"stopping-program"},
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


if __name__ == "__main__":
    unittest.main()
