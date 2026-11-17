"""Select Lean CI jobs from the complete Git tree diff for this run."""

from fnmatch import fnmatchcase
import os
from pathlib import Path
import subprocess


# A project proof can be imported across audit families. Recheck the suite on
# proof, build-system, shared verifier, or workflow changes.
SHARED = (
    ".github/workflows/checks.yml", ".github/lean_ci.py", ".gitattributes",
    "lean/*.lean", "lean/lean-toolchain", "lean/lakefile.*", "lean/lake-manifest.json",
    "tools/verify_blind_upper_components.py", "tools/verify_tier6.py",
)

# Basenames of the Python verifiers each job runs or imports, including helpers
# used by more than one job. Keep research-only verifiers out of these groups.
VERIFIERS = {
    "lean-all-modules": "project_axioms",
    "lean-kernel": """
        lean_checkpoint uniform_arithmetic uniform713 tier[345] critical_components
        critical_all_sizes critical_psi critical_upper_components unbiased_converse
        observable713 confidence oracle_lower rare_above_two quantile_comparison
        selection_approximation finite_selection_approximation deterministic_certificates
        finite_law_certificates envelope_transfer_certificates global_selection_certificates
        entropy_tail_components sharp_rms project_axioms
    """,
    "entropy-tail-upper": """
        entropy_tail entropy_tail_components entropy_tail_sharp entropy_tail_upper
        closed_quantile finite_quantile quantile_comparison quantile_selection quantile_price_upper
        quantile_sharp_law quantile_optimality optimal_quantile bandwise_suffix selection_stability
        quarter_smoothing confidence_* critical_confidence hard_budget stopping_confidence
        stochastic_envelope sublinear_power shifted_power anytime_* smooth_density observed_*
        continuous_observed typed_confidence additive_confidence psi_* power_window rms_localization
        band_cost_selection gap_law_menus law_adaptation* arbitrary_law_* known_law_*
        dyadic_summability robust_* clipping_pilot_independence paid_median project_axioms
    """,
    "stopping-program": """
        stopping_components stopping_flow_mixture finite_stopping_program rarity_support
        stopping_dual information_bellman reference_absorption ordered_information
        adaptive_information stopping_program_upper finite_risk_certificate infinite_cap_dual
        genie_* finite_cap_truncation entropy_tail entropy_tail_components entropy_tail_lower_components
        square_root_cap sharp_rms
    """,
}

DATA = {
    "lean-all-modules": ("tools/definition_lock.json",),
    "lean-kernel": (
        "FROZEN.sha256", "TIER*_FROZEN.sha256",
        "proposals/constants/UniformArithmetic.lean", "results/lean_best.json",
        "lean/ThresholdHC/*/SPEC*.json", "lean/ThresholdHC/ResearchRouteA/verify.py",
        "tools/test_*_certificates_audit.py", "toolkit/tests/test_*_certificates.py",
        "toolkit/threshold_toolkit/*.py", "tools/blind_upper_components.json",
        "tools/blind_upper_specification_freeze.json", "tools/critical_all_sizes_specification_lock.json",
        "tools/critical_psi_specification_freeze.json", "tools/critical_upper_specification_freeze.json",
        "tools/confidence_specification_freeze.json", "tools/observable713_specification_freeze.json",
        "tools/oracle_lower_specification_freeze.json", "tools/rare_above_two_specification_freeze.json",
        "tools/unbiased_converse_specification_freeze.json", "tools/quantile_comparison_specification_freeze.json",
    ),
    "entropy-tail-upper": (
        "lean/ThresholdHC/HardBudget/SPECIFICATION.sha256", "tools/closed_quantile_specification_freeze.json",
        "tools/entropy_tail_specification_freeze.json", "tools/entropy_tail_quantile_specification_freeze.json",
        "tools/quantile_comparison_specification_freeze.json",
    ),
    "stopping-program": (
        "tools/stopping_program_lock.py", "tools/stopping_program_specification_freeze.json",
        "tools/entropy_tail_lower_specification_freeze.json", "tools/entropy_tail_specification_freeze.json",
    ),
}


def frozen_inputs():
    # The kernel scorer and tier audits read every entry, including constants/
    # and Python tools. Cone-mode sparse checkout includes these root manifests.
    paths = set()
    for manifest in Path(".").glob("*FROZEN.sha256"):
        paths.add(manifest.name)
        for line in manifest.read_text(encoding="utf-8").splitlines():
            if line.strip() and not line.startswith("#"):
                paths.add(line.split(maxsplit=1)[1])
    return paths


def select_jobs(paths):
    if paths is None or any(fnmatchcase(p, pattern) for p in paths for pattern in SHARED):
        return set(VERIFIERS)

    selected = {"lean-kernel"} if paths & frozen_inputs() else set()
    for job, verifiers in VERIFIERS.items():
        patterns = [f"tools/verify_{name}.py" for name in verifiers.split()]
        patterns.extend(DATA[job])
        if any(fnmatchcase(p, pattern) for p in paths for pattern in patterns):
            selected.add(job)
    return selected


def changed_paths(base, head):
    # Manual runs have no base. A new ref or a force-push may have no reachable
    # previous tree either. Run all audits whenever we cannot establish the diff.
    if not base or not base.strip("0"):
        return None
    diff = subprocess.run(
        ["git", "diff", "--name-only", "--no-renames", "-z", base, head, "--"],
        stdout=subprocess.PIPE,
    )
    if diff.returncode:
        return None
    return {os.fsdecode(path) for path in diff.stdout.split(b"\0") if path}


if __name__ == "__main__":
    paths = changed_paths(os.environ["BASE_SHA"], os.environ["GITHUB_SHA"])
    selected = select_jobs(paths)
    print("Changed paths:", len(paths) if paths is not None else "full run")
    print("Selected Lean jobs:", ", ".join(sorted(selected)) or "none")
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as output:
        for job in VERIFIERS:
            print(f"{job}={str(job in selected).lower()}", file=output)
