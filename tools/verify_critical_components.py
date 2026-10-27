"""Check critical single-coin base cost and components, not the full minimax law.

This extension does not change existing frozen targets or scores. It reuses the
frozen Tier 6 source and transitive-axiom guards. Specifications were introduced
with these proofs, not retrospectively described as a pre-proof freeze.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

from verify_tier6 import ALLOWED, DECLARATION, FORBIDDEN, REPORT, strip_comments

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
SOURCE = LEAN / "ThresholdHC/CriticalEntropy"
MODULES = ("Packing", "CommonPoint", "BernoulliPrefix", "EventInformation", "SignTest",
           "EarlyDecision", "StoppingWindow", "GeometricOverlap", "FiniteGap",
           "StoppedModel", "StoppedTape", "SequentialModel", "RestartPair",
           "RepeatedModel", "RepeatedRestart", "RepeatedSignModel", "SampleMean",
           "SignReduction", "EstimationEntropy", "PopulationModel", "UniformCoin",
           "PopulationMixture", "PopulationVariance", "GoodGapModel", "ConditionalMoments",
           "HalfPrior", "GapSelection", "GoodGaps", "CriticalModel", "CriticalLaw",
           "CriticalAnnuli", "CriticalScale", "ActivationModel", "Activation", "ActivationCost",
           "ScaleAsymptotics", "BaseCost",
           "ObservationModel", "FiniteObservation", "CappedObservation", "FiniteSufficiency",
           "LikelihoodBounds", "HellingerModel", "Hellinger", "ObservationInformation", "Specification")
NAMESPACE = "ThresholdHC.CriticalEntropy."
ROOTS = {
    NAMESPACE + name for name in (
        "sum_event_mass_le_overlap", "event_packing", "overlap_bound",
        "entropy_of_packing", "entropy_of_gap_count", "finite_common_point",
        "common_point_of_finite_mixtures", "EntropyPackingStatement", "CommonPointStatement",
        "streamProb_pos", "stream_kl_identity", "finiteMeasure_positive", "finiteMeasure_density",
        "seeded_prefix_kl", "binary_kl_le_chisq", "seeded_prefix_kl_le_chisq",
        "seeded_tape_prefix_map", "prefix_observable_kl_le", "binary_kl_lower_log",
        "event_binary_kl_le", "event_mass_lower_of_kl", "prefix_event_mass_lower",
        "fair_prefix_event_mass_lower", "PrefixInformationStatement", "PrefixEventTransferStatement",
        "SignTest", "signTestWork", "expectedSignTestWork", "signTestWindow",
        "measurable_signTestWork", "measurable_signTestWindow", "signTest_prefix_probability",
        "signTest_terminates", "signTest_late_probability", "signTest_window_probability",
        "binary_kl_separation", "early_event_probability", "EntropyGap", "signParameter",
        "signParameter_interior", "early_prefix_information", "signTest_early_minus",
        "entropyLowerTime", "entropyUpperTime", "entropyLowerTime_bounds", "entropyUpperTime_bounds",
        "signTest_quarter_late", "signTest_negative_window", "restrictPrefix", "signTestWindowPrefix",
        "measurable_signTestWindowPrefix", "signTestWindowPrefix_preimage", "signTestWindowPrefix_probability",
        "signTestWindow_positive_imp_lt", "signTest_fair_window", "signTest_window_scale",
        "geometric_separation_of_adjacent", "half_low_cost", "geometric_interval_card",
        "inverse_gap_scales_separated", "signTest_window_overlap", "finite_gap_sign_entropy",
        "FiniteGapSignEntropyStatement",
        "tapeDrop", "measurable_tapeDrop", "StoppedProcedure", "stoppedSuffix",
        "measurable_stoppedSuffix", "stoppedProcedureWork", "expectedStoppedProcedureWork",
        "measurable_stoppedProcedureWork", "stoppedWithWork", "tapeDrop_map",
        "prefix_drop_independent", "tape_split_map", "seeded_tape_split_map",
        "measure_eq_tsum_stopping", "seeded_prefix_drop_probability",
        "stopped_event_tail_probability", "stopped_output_suffix_probability",
        "stopped_output_suffix_map", "stopped_procedure_terminates", "stopped_marked_suffix_map",
        "StoppedSuffixStatement",
        "completePrefix", "measurable_completePrefix", "tapePrefix_completePrefix",
        "prefix_eq_restrict", "prefix_eq_drop", "stopped_prefix_ext", "restartInput",
        "measurable_restartInput", "sequentialStop", "sequentialOutput",
        "measurable_sequentialStop", "measurable_sequentialOutput", "sequential_prefix_ext",
        "sequentialProcedure", "prod_swap_middle", "seeded_stopped_suffix_map",
        "two_run_marked_map", "two_run_expected_work", "sequential_expected_work",
        "sequential_output_map", "SequentialRestartStatement",
        "reseedProcedure", "postprocessProcedure", "emptyProcedure", "measurable_finCons",
        "repeatedProcedure", "fin_seed_split_map", "reseed_expected_work",
        "repeated_expected_work", "reseed_output_map", "fin_product_cons_map",
        "repeated_output_map", "RepeatedRestartStatement",
        "stopped_before_prefix_ext", "stoppedToSignTest", "repeatedSignDecision",
        "measurable_repeatedSignDecision", "repeatedSignTest", "iid_sum_memLp",
        "iid_sum_integral", "iid_sum_variance", "iid_sum_deviation", "iid_sum_lower_error",
        "iid_sum_upper_error", "repeated_sign_work", "repeated_sign_plus_error",
        "repeated_sign_minus_error", "finite_gap_estimation_entropy", "critical_restart_count_bounds",
        "RepeatedSignTestStatement", "FiniteGapEstimationEntropyStatement",
        "uniformUnitMeasure", "uniformUnitMeasure_probability", "uniformCoinFlip",
        "measurable_uniformCoinFlip", "uniformTapeMeasure", "uniformTapeMeasure_probability",
        "uniformCoinTape", "measurable_uniformCoinTape", "uniformProcedureState",
        "measurable_uniformProcedureState", "conditionalSecondMoment", "conditionalMean",
        "mixtureParameter", "measurable_mixtureParameter", "populationInput",
        "measurable_populationInput", "populationMeasure", "populationSecondMoment",
        "populationExpectedWork", "populationMean", "uniformCoinFlip_true", "uniformCoinFlip_map",
        "uniformCoinTape_map", "seeded_uniformCoinTape_map", "conditionalSecondMoment_uniform",
        "conditionalMean_uniform", "conditionalWork_uniform", "measurable_conditionalSecondMoment",
        "measurable_conditionalMean", "measurable_conditionalWork", "conditionalSecondMoment_finite_iff",
        "conditionalMean_output_law", "conditionalSecondMoment_output_law", "seeded_lintegral_uniform",
        "measurable_seeded_lintegral", "measurable_seeded_integral", "conditionalMean_integrable_of_moment",
        "mixtureParameter_map", "lintegral_bernoulli_parameter", "mixtureParameter_lintegral",
        "population_lintegral", "population_lintegral_const", "population_finite_components",
        "population_ae_finite_components", "mixtureParameter_integral", "population_integral",
        "population_finite_all", "population_conditional_finiteness", "population_second_moment_formula",
        "population_work_formula", "population_mean_formula", "population_finiteness_transfer",
        "PopulationMomentStatement", "PopulationFinitenessStatement",
        "population_memLp_of_moment", "population_second_moment_toReal", "variance_lower_of_mixture",
        "population_second_moment_const", "population_mean_const", "population_variance_mixture_lower",
        "population_variance_floor", "conditionalMean_sq_le_moment", "population_moment_bound_of_variance",
        "population_moment_finite_of_evariance", "population_evariance_floor",
        "population_moment_bound_of_evariance", "CappedPrior", "halfPrior", "CappedPopulationGuarantee",
        "PopulationGoodGap", "conditional_moment_pair_integrable", "population_second_moment_real_formula",
        "measurable_halfPrior", "halfPrior_le_half", "halfPrior_integral", "cappedPrior_const",
        "cappedPrior_half", "halfPrior_weighted_integral", "population_halfPrior_moment", "population_halfPrior_mean",
        "exists_subset_real_measure", "bad_set_mass_lt_of_integral_lower", "bad_set_mass_lt_of_integral_upper",
        "population_good_gaps", "PopulationVarianceFloorStatement", "PopulationMomentFromVarianceStatement",
        "PopulationGoodGapsStatement",
        "criticalGapLaw", "criticalUpper", "criticalAnnulus",
        "criticalParameter", "criticalGapLaw_noAtoms", "linear_density_interval",
        "criticalGapLaw_Ioc", "criticalGapLaw_supported", "criticalGapLaw_probability",
        "criticalGapLaw_real_Ioc", "criticalUpper_pos", "criticalUpper_le_quarter",
        "criticalUpper_succ", "criticalAnnulus_mass", "criticalAnnulus_adjacent",
        "criticalUpper_antitone", "criticalAnnulus_disjoint", "measurable_criticalParameter",
        "criticalParameter_eq_sign", "criticalParameter_coe_of_mem", "exists_good_point_low_work",
        "criticalAnnulus_work_factor", "critical_annulus_work_sum", "critical_annulus_good_points",
        "population_negative_work_integral", "critical_scale_entropy", "critical_scale_product",
        "CriticalLawStatement", "CriticalScaleProductStatement",
        "activeSeeds", "measurableSet_activeSeeds", "stop_zero_iff_inactive",
        "inactive_output", "inactive_work", "active_work_lower",
        "activation_work_restrict", "activation_conditional_work", "activation_probability_le_work",
        "activation_conditional_work_lower", "normalized_event_mean", "normalized_event_moment",
        "populationSeedEvent", "measurableSet_populationSeedEvent", "populationSeedEvent_measure",
        "populationMeasure_restrict_seed", "populationMeasure_smul_seed", "populationMeasure_condition_seed",
        "population_inactive_mean", "activeProcedure", "population_activation_mean",
        "population_activation_work", "activation_positive_of_bias", "population_activation_moment",
        "active_population_guarantee", "capped_guarantee_moment_floor", "population_null_work_ge_activation",
        "activation_product_bounds", "critical_product_scale", "entropy_scale_count",
        "critical_annulus_mass_of_small_product", "entropy_logs_le_exp", "criticalLogFactor",
        "critical_scalar_base_cost", "critical_raw_base_cost", "critical_base_cost",
        "ActivationNormalizationStatement", "CriticalRawBaseCostStatement", "CriticalBaseCostStatement",
        "wordHeads", "stoppedSeedCell", "wordLikelihood",
        "populationWordLikelihood", "CappedWord", "cappedWord_fintype",
        "cappedWord_measurableSpace", "cappedWord_measurableSingleton", "cappedTranscript",
        "cappedTranscriptLaw", "stoppedReference", "stoppedStatistic",
        "cappedStatisticLaw", "transcriptReconstruction", "streamProb_heads",
        "measurableSet_stoppedSeedCell", "stopped_word_probability", "population_event_probability",
        "measurable_wordLikelihood", "population_stopped_word_probability", "population_stopped_heads_probability",
        "measurable_cappedTranscript", "cappedTranscript_of_stop", "cappedTranscript_mem_cell",
        "cappedTranscriptLaw_cell", "stoppedReference_cell", "measure_ext_prod_finite",
        "stoppedReference_finite", "cappedTranscriptLaw_density", "cappedTranscriptLaw_probability",
        "map_factored_density", "factored_density_restrict", "factored_density_fiber_mass",
        "factored_density_cond", "cappedStatisticLaw_density", "wordLikelihood_le_one",
        "wordLikelihood_pos", "prior_weights_sum", "populationWordLikelihood_le_one",
        "populationWordLikelihood_pos", "critical_parameters_interior", "hellingerAffinity",
        "finiteAffinity", "affinity_density_scaling", "hellingerAffinity_withDensity",
        "affinity_mass_scaling", "hellingerAffinity_finite_density", "cappedStatisticLaw_probability",
        "cappedStatisticLaw_zero_iff_reference", "hellingerAffinity_factored_statistic", "capped_observation_reconstruction",
        "capped_observation_affinity", "capped_observation_finite_affinity", "capped_transcript_work",
        "capped_observation_work", "critical_observation_reconstruction", "critical_observation_finite_affinity",
        "critical_observation_work", "CriticalObservationReconstructionStatement", "CriticalObservationAffinityStatement",
        "CriticalObservationWorkStatement",
    )
}


def validate_reports(output: str, returncode: int) -> dict[str, list[str]]:
    if returncode != 0:
        raise ValueError("Lean audit exited unsuccessfully")
    reports: dict[str, list[str]] = {}
    for name, _kind, axioms in REPORT.findall(output):
        if name in reports:
            raise ValueError("Duplicate audit root: " + name)
        reports[name] = [a.strip() for a in axioms.split(",") if a.strip()]
    if set(reports) != ROOTS:
        raise ValueError("Missing or unexpected audit roots")
    if any(set(axioms) - ALLOWED for axioms in reports.values()):
        raise ValueError("Disallowed transitive axiom")
    return reports


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    output = args.output_dir or ROOT / ".runtime/critical-components" / datetime.now(
        timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    sources = sorted(SOURCE.glob("*.lean"))
    expected_sources = {name + ".lean" for name in (*MODULES, "Audit")}
    if {p.name for p in sources} != expected_sources:
        raise ValueError("Unexpected or missing component module")
    declared = []
    for path in sources:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        imports = re.findall(r"^import\s+([\w.]+)\s*$", source, re.M)
        allowed_imports = {
            "Mathlib", "Mathlib.MeasureTheory.Integral.Prod",
            "Mathlib.InformationTheory.KullbackLeibler.DataProcessing",
            "Mathlib.Analysis.SpecialFunctions.BinaryEntropy",
            "ThresholdHC.Proofs.Tier2.ClassifierProbability",
            "ThresholdHC.Proofs.Tier2.TranscriptLikelihood",
            "ThresholdHC.Tier4.FiniteDensity", "ThresholdHC.Tier6.TestingFinite",
        } | {NAMESPACE + name for name in MODULES}
        if any(module not in allowed_imports for module in imports):
            raise ValueError("Unregistered component import in " + path.name)
        declared.extend(NAMESPACE + name for name in DECLARATION.findall(source))
    if len(declared) != len(ROOTS) or set(declared) != ROOTS:
        raise ValueError("Public declaration coverage mismatch")
    protected = sources + [Path(__file__).resolve(), ROOT / "tools/verify_tier6.py",
                           LEAN / "lean-toolchain", LEAN / "lake-manifest.json"]
    hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in protected}
    status = {
        "valid": False,
        "scope": "Critical quadratic single-coin variance and raw-moment base-cost bounds for all rarities, derived from actual observable population experiments; activation, scale selection, restarts, sign entropy, finite stopped-observation reconstruction, canonical affinity and work preservation, and abstract common point",
        "full_critical_minimax_theorem_verified": False,
        "base_cost_theorem_verified": False,
        "capped_observation_reduction_verified": False,
        "finite_gap_sign_testing_theorem_verified": False,
        "stopped_suffix_independence_verified": False,
        "sequential_restart_law_and_work_verified": False,
        "finite_repetition_iid_and_work_verified": False,
        "repeated_sign_error_and_work_verified": False,
        "finite_gap_estimation_entropy_verified": False,
        "population_moment_disintegration_verified": False,
        "population_conditional_finiteness_verified": False,
        "population_extended_variance_floor_verified": False,
        "population_moment_from_variance_verified": False,
        "population_good_gap_selection_verified": False,
        "critical_gap_law_verified": False,
        "critical_scale_null_cost_product_verified": False,
        "activation_normalization_verified": False,
        "critical_raw_base_cost_verified": False,
        "specifications_frozen_before_proofs": False,
        "source_sha256": hashes,
        "commands": [],
    }
    status_path = output / "status.json"
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    build = LEAN / ".lake/build/lib/lean/ThresholdHC/CriticalEntropy"
    build.mkdir(parents=True, exist_ok=True)
    commands = [["lake", "env", "lean", "-o", str(build / (name + ".olean")),
                 "ThresholdHC/CriticalEntropy/" + name + ".lean"] for name in MODULES]
    commands.append(["lake", "env", "lean", "ThresholdHC/CriticalEntropy/Audit.lean"])
    for index, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True,
                                encoding="utf-8")
        text = result.stdout + result.stderr
        (output / f"{index + 1:02d}.log").write_text(text, encoding="utf-8")
        status["commands"].append({"command": command, "exit_code": result.returncode})
        status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        if result.returncode:
            print(text)
            return result.returncode
    status["axioms"] = validate_reports(text, result.returncode)
    if any(hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest
           for rel, digest in hashes.items()):
        raise ValueError("Sources changed during audit")
    status.update(valid=True, exact_component_targets=23, audited_declarations=len(ROOTS),
                  finite_gap_sign_testing_theorem_verified=True,
                  stopped_suffix_independence_verified=True,
                  sequential_restart_law_and_work_verified=True,
                  finite_repetition_iid_and_work_verified=True,
                  repeated_sign_error_and_work_verified=True,
                  finite_gap_estimation_entropy_verified=True,
                  population_moment_disintegration_verified=True,
                  population_conditional_finiteness_verified=True,
                  population_extended_variance_floor_verified=True,
                  population_moment_from_variance_verified=True,
                  population_good_gap_selection_verified=True,
                  critical_gap_law_verified=True,
                  critical_scale_null_cost_product_verified=True,
                  activation_normalization_verified=True,
                  critical_raw_base_cost_verified=True,
                  base_cost_theorem_verified=True,
                  capped_observation_reduction_verified=True)
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"valid": True, "exact_component_targets": 23,
                      "audited_declarations": len(ROOTS), "evidence": str(output),
                      "finite_gap_sign_testing_theorem_verified": True,
                      "stopped_suffix_independence_verified": True,
                      "sequential_restart_law_and_work_verified": True,
                      "finite_repetition_iid_and_work_verified": True,
                      "repeated_sign_error_and_work_verified": True,
                      "finite_gap_estimation_entropy_verified": True,
                      "population_moment_disintegration_verified": True,
                      "population_conditional_finiteness_verified": True,
                      "population_extended_variance_floor_verified": True,
                      "population_moment_from_variance_verified": True,
                      "population_good_gap_selection_verified": True,
                      "critical_gap_law_verified": True,
                      "critical_scale_null_cost_product_verified": True,
                      "activation_normalization_verified": True,
                      "critical_raw_base_cost_verified": True,
                      "base_cost_theorem_verified": True,
                      "capped_observation_reduction_verified": True,
                      "full_critical_minimax_theorem_verified": False}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
