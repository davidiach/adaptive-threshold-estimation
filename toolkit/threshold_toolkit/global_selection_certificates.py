"""Kernel certificates for bounded global menu, DP and approximation outputs.

This checks a projection of the unchanged producers' numerical results. It
enumerates a complete suffix menu, independently of the producer's pruning.
It does not certify Python execution, internal state counts or polynomial cost.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
from itertools import product
from pathlib import Path
import subprocess
from typing import Any

from . import deterministic_certificates as dc
from . import finite_law_certificates as fc
from .band_cost_selection import select_by_band_cost
from .approximate_selection import select_approximately
from .rare_event_functional import FiniteGapLaw, Interval, Precision, band_index, exhaustive_certificate

VerificationError = dc.VerificationError
SCHEMA = "ate-kernel-global-selection-v1"
MAX_ATOMS = 6


@dataclass(frozen=True)
class Request:
    operation: str
    atoms: tuple[tuple[F, F], ...]
    rho: F = F(1, 4)
    budget: F = F(16)
    epsilon: F = F(1, 10)
    bits: int = 80
    log_terms: int = 32
    max_work: int = 4096

    def __post_init__(self) -> None:
        if type(self.operation) is not str or self.operation not in ("exhaustive", "dp", "approximate"):
            raise VerificationError("Supported operations: exhaustive, dp, approximate.")
        if type(self.atoms) is not tuple or not 1 <= len(self.atoms) <= MAX_ATOMS:
            raise VerificationError("Supply 1 to 6 canonical atoms.")
        checked = fc.Request("objective", self.atoms, tuple(F(0) for _ in self.atoms),
                             rho=self.rho, budget=self.budget, bits=self.bits, log_terms=self.log_terms)
        for name in ("atoms", "rho", "budget"):
            object.__setattr__(self, name, getattr(checked, name))
        object.__setattr__(self, "epsilon", dc._exact(self.epsilon))
        if not 0 < self.epsilon <= 1:
            raise VerificationError("Require epsilon in (0,1].")
        if type(self.max_work) is not int or not 1 <= self.max_work <= 4096:
            raise VerificationError("max_work must be an integer in [1,4096].")

    def as_dict(self) -> dict:
        return dict(operation=self.operation, atoms=[[str(d), str(w)] for d, w in self.atoms],
                    rho=str(self.rho), budget=str(self.budget), epsilon=str(self.epsilon),
                    bits=self.bits, log_terms=self.log_terms, max_work=self.max_work)


def _menu(request: Request) -> list[int]:
    groups: dict[int, list[int]] = {}
    for i, (d, _) in enumerate(request.atoms):
        groups.setdefault(band_index(d), []).append(i)
    menus = [[sum(1 << i for i in group[len(group)-k:]) for k in range(len(group)+1)]
             for group in groups.values()]
    return [sum(choices) for choices in product(*menus)]


def produce(request: Request) -> dict:
    """Call an unchanged producer; attach an untrusted complete-menu witness."""
    law = FiniteGapLaw(request.atoms)
    common = dict(rho=request.rho, budget=request.budget,
                  precision=Precision(request.bits, request.log_terms))
    if request.operation == "exhaustive":
        raw = exhaustive_certificate(law, **common, max_states=request.max_work)
        selected = raw["details"]["best_hard_witness"]
        out = dict(value=raw["K_interval"], selected=None if selected is None else [s == "1" for s in selected],
                   suffix_count=raw["details"]["states_evaluated"])
    elif request.operation == "dp":
        raw = select_by_band_cost(law, **common, max_transitions=request.max_work)
        out = dict(value=raw.value.as_dict(), selected=list(raw.selected), suffix_count=raw.suffix_count,
                   optimality_proved=raw.optimality_proved)
    else:
        raw = select_approximately(law, **common, epsilon=request.epsilon, max_transitions=request.max_work)
        out = dict(value=raw.value.as_dict(), selected=list(raw.selected), suffix_count=raw.suffix_count,
                   witness_value=raw.witness_value.as_dict(), epsilon=str(raw.epsilon))
    certificate = dict(schema=SCHEMA, request=request.as_dict(), output=out, menu=_menu(request))
    _snapshot(request, certificate)
    return certificate


def _same(a: Any, b: Any) -> bool:
    if type(a) is not type(b):
        return False
    if type(b) is dict:
        return a.keys() == b.keys() and all(_same(a[k], v) for k, v in b.items())
    if type(b) is list:
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b))
    return a == b


def _snapshot(expected: Request, certificate: Any) -> dict:
    if type(certificate) is not dict or set(certificate) != {"schema", "request", "output", "menu"}:
        raise VerificationError("Unexpected certificate fields.")
    if type(certificate["schema"]) is not str or certificate["schema"] != SCHEMA:
        raise VerificationError("Unknown schema.")
    if not _same(certificate["request"], expected.as_dict()):
        raise VerificationError("Certificate does not match the caller's expected request.")
    out = certificate["output"]
    fields = {"value", "selected", "suffix_count"}
    if expected.operation == "dp":
        fields.add("optimality_proved")
    elif expected.operation == "approximate":
        fields.update(("witness_value", "epsilon"))
    if type(out) is not dict or set(out) != fields:
        raise VerificationError("Unexpected output fields.")
    def number(x: Any) -> str:
        if type(x) is not str:
            raise VerificationError("Require exact rational strings.")
        return str(dc._exact(x, dc.MAX_ENDPOINT_BITS))
    def interval(x: Any) -> dict:
        if type(x) is not dict or set(x) != {"lower", "upper"}:
            raise VerificationError("Malformed interval.")
        result = {k: number(x[k]) for k in ("lower", "upper")}
        if F(result["lower"]) > F(result["upper"]):
            raise VerificationError("Reversed interval.")
        return result
    selected = out["selected"]
    if selected is None:
        if expected.operation != "exhaustive":
            raise VerificationError("This producer must return a witness.")
    elif type(selected) is not list or len(selected) != len(expected.atoms) or any(type(s) is not bool for s in selected):
        raise VerificationError("Require one Boolean selection per atom.")
    count = out["suffix_count"]
    if type(count) is not int or not 1 <= count <= 2**len(expected.atoms):
        raise VerificationError("Invalid suffix count.")
    result = dict(value=interval(out["value"]), selected=None if selected is None else list(selected), suffix_count=count)
    if expected.operation == "dp":
        if type(out["optimality_proved"]) is not bool:
            raise VerificationError("Optimality flag must be Boolean.")
        result["optimality_proved"] = out["optimality_proved"]
    if expected.operation == "approximate":
        result.update(witness_value=interval(out["witness_value"]), epsilon=number(out["epsilon"]))
    menu = certificate["menu"]
    if type(menu) is not list or not 1 <= len(menu) <= 2**len(expected.atoms) or any(
            type(s) is not int or not 0 <= s < 2**len(expected.atoms) for s in menu):
        raise VerificationError("Malformed bounded menu.")
    return dict(schema=SCHEMA, request=expected.as_dict(), output=result, menu=list(menu))


def _mask(mask: int, n: int) -> str:
    return fc._vec(("true" if mask & (1 << i) else "false" for i in range(n)), "Bool")


def proof_source(expected: Request, certificate: Any) -> str:
    """Generate a closed theorem; only successful kernel verification accepts it."""
    snapshot = _snapshot(expected, certificate)
    r, out, menu = expected, snapshot["output"], snapshot["menu"]
    n = len(r.atoms)
    bands = tuple(band_index(d) for d, _ in r.atoms)
    labels = tuple(sorted(set(bands)))
    selected = out["selected"] or [False]*n
    witness = sum(1 << i for i, s in enumerate(selected) if s)
    lo, hi = F(out["value"]["lower"]), F(out["value"]["upper"])
    wlo, whi = (F(out["witness_value"][k]) for k in ("lower", "upper")) if r.operation == "approximate" else (F(0), hi)
    rho, budget = dc._q(r.rho), dc._q(r.budget)
    coordinates = ', '.join(f's {i}' for i in range(n))
    splits = ' <;> '.join(f'cases h{i} : s {i}' for i in range(n))
    bit_facts = ', '.join(f'h{i}' for i in range(n))
    source = f"""import ThresholdHC.GlobalSelectionCertificates.Trace
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.FiniteLawCertificates ThresholdHC.DeterministicCertificates
open ThresholdHC.GlobalSelectionCertificates
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
private def gaps := {fc._vec(d for d, _ in r.atoms)}
private def weights := {fc._vec(w for _, w in r.atoms)}
private def labels := {fc._vec(labels, 'ℕ')}
private def bands := {fc._vec(bands, 'ℕ')}
private def candidates : List (Fin {n} → Bool) := [{', '.join(_mask(s,n) for s in menu)}]
private def witness := {_mask(witness,n)}
private theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem weights_positive : ∀ i, 0 < weights i := by norm_num [weights, Fin.forall_fin_succ]
private theorem weights_valid : ∀ i, 0 ≤ weights i := fun i => (weights_positive i).le
private theorem weights_sum : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
private theorem labels_injective : Function.Injective labels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [labels] at *
private theorem bands_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true := by
  norm_num [gaps, labels, inBand, Fin.forall_fin_succ, Fin.exists_fin_succ]
private theorem bands_valid : ∀ i, inBand (gaps i) (bands i) = true := by
  norm_num [gaps, bands, inBand, Fin.forall_fin_succ]
private noncomputable def law := atomicMeasure (points gaps gaps_valid) weights
private noncomputable def K := (ThresholdHC.EntropyTail.selection law ({rho}:ℝ) ({budget}:ℝ)).toReal
private noncomputable def J (s : Fin {n} → Bool) := (objectiveExpr gaps weights (fractions s) labels {rho} {budget}).eval
private theorem attained : ∃ s, suffixCheck gaps bands s = true ∧ K = J s :=
  suffix_attains gaps weights labels bands {rho} {budget} gaps_valid weights_positive weights_sum
    labels_injective bands_cover bands_valid (by norm_num) (by norm_num) (by norm_num)
private theorem complete_menu : ∀ s, suffixCheck gaps bands s = true → s ∈ candidates := by
  intro s hs
  have he : s = ![{coordinates}] := by funext i; fin_cases i <;> rfl
  rw [he] at hs ⊢
  {splits} <;> simp only [{bit_facts}] at hs ⊢ <;>
    norm_num [suffixCheck, gaps, bands, Fin.forall_fin_succ] at hs <;> norm_num [candidates]
private theorem menu_valid : candidates.Nodup ∧ (∀ s ∈ candidates, suffixCheck gaps bands s = true) ∧
    candidates.length = {out['suffix_count']} := by
  norm_num [candidates, suffixCheck, gaps, bands, Fin.forall_fin_succ] <;> decide
private theorem witness_suffix : suffixCheck gaps bands witness = true := by
  norm_num [witness, suffixCheck, gaps, bands, Fin.forall_fin_succ]
private theorem feasible : K ≤ J witness :=
  selection_le_expr gaps weights (fractions witness) labels {rho} {budget} gaps_valid weights_valid
    (fractions_valid witness) (by norm_num) (by norm_num) labels_injective bands_cover
"""
    # Stronger internal precision can prove producer intervals formed with a
    # different order of additions. Exhaustion is rejection, never acceptance.
    bits, terms = min(512, 2*r.bits), min(256, 2*r.log_terms)
    def objective(mask: int, lower: F, upper: F, name: str) -> str:
        fractions = tuple(F(bool(mask & (1 << i))) for i in range(n))
        request = fc.Request("objective", r.atoms, fractions, rho=r.rho, budget=r.budget,
                             bits=bits, log_terms=terms)
        if lower > upper:
            raise VerificationError("Claimed lower bound exceeds the objective cap.")
        claimed = Interval(lower, upper)
        evidence = fc._objective_evidence(request, claimed, labels)
        return f"""private theorem {name} : Contains {dc._interval(claimed)} (J {_mask(mask,n)}) := by
  apply accepted_sound (e := objectiveExpr gaps weights (fractions {_mask(mask,n)}) labels {rho} {budget})
  norm_num [gaps, weights, labels, fractions, {fc._REDUCE.replace(', tailWorkExpr, tailWeights', '')}]
""".replace("  norm_num [", f"  change accepted _ _ {evidence} = true\n  norm_num [", 1)
    # Bind the witness interval itself, not only the global upper endpoint.
    source += objective(witness, wlo, whi, "witness_bounds")
    exact_optimum = out.get("optimality_proved", False)
    for i, mask in enumerate(menu):
        lower = max(lo, whi) if exact_optimum and mask != witness else lo
        source += objective(mask, lower, r.rho, f"candidate_{i}")
    source += f"""private theorem lower_bounds : ∀ s ∈ candidates, ({dc._q(lo)}:ℝ) ≤ J s := by
  intro s hs
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with {' | '.join('rfl' for _ in menu)}
"""
    for i in range(len(menu)):
        source += f"  · have h := (candidate_{i}).1\n    dsimp [Contains] at h\n    linarith\n"
    source += f"""private theorem enclosure : ({dc._q(lo)}:ℝ) ≤ K ∧ K ≤ J witness ∧ J witness ≤ ({dc._q(hi)}:ℝ) := by
  apply global_enclosure (fun s => suffixCheck gaps bands s = true) J K candidates witness
    {dc._q(lo)} {dc._q(hi)} attained complete_menu lower_bounds feasible
  have h := witness_bounds.2
  change J witness ≤ ({dc._q(whi)}:ℝ) at h
  have hu : ({dc._q(whi)}:ℝ) ≤ ({dc._q(hi)}:ℝ) := by norm_num
  exact h.trans hu
"""
    extra_claim, extra_proof = "True", "trivial"
    if out['selected'] is None:
        extra_claim, extra_proof = f"({dc._q(hi)}:ℚ) = {rho}", "by norm_num"
    if exact_optimum:
        source += "private theorem optimal : J witness = K := by\n"
        source += "  apply global_optimality (fun s => suffixCheck gaps bands s = true) J K candidates witness attained complete_menu _ feasible\n"
        source += "  intro s hs\n  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hs\n"
        source += f"  rcases hs with {' | '.join('rfl' for _ in menu)}\n"
        for i, mask in enumerate(menu):
            if mask == witness:
                source += "  · exact le_rfl\n"
            else:
                source += f"  · have hl := candidate_{i}.1\n    have hu := witness_bounds.2\n    dsimp [Contains] at hl hu\n    change J witness ≤ _ at hu\n    linarith\n"
        extra_claim, extra_proof = "J witness = K", "optimal"
    elif r.operation == "approximate":
        eps = dc._q(r.epsilon)
        extra_claim = f"0 < ({dc._q(lo)}:ℝ) ∧ ({dc._q(F(out['epsilon']))}:ℚ) = {eps} ∧ ({dc._q(hi)}:ℚ) ≤ (1+{eps})*{dc._q(lo)} ∧ J witness ≤ (1+({eps}:ℝ))*K ∧ Contains {dc._interval(Interval(wlo,whi))} (J witness)"
        extra_proof = f"by refine ⟨by norm_num, by norm_num, by norm_num, ?_, witness_bounds⟩; exact relative_certificate (by norm_num : (0:ℚ) ≤ {eps}) enclosure (by norm_num)"
    source += f"""theorem certified_value : IsProbabilityMeasure law ∧
    Contains {dc._interval(Interval(lo,hi))} K ∧
    atomicMeasure (points gaps gaps_valid) (fun i => weights i*fractions witness i) ≤ law ∧
    suffixCheck gaps bands witness = true ∧
    K ≤ J witness ∧ J witness ≤ ({dc._q(hi)}:ℝ) ∧
    candidates.Nodup ∧ (∀ s ∈ candidates, suffixCheck gaps bands s = true) ∧
    (∀ s, suffixCheck gaps bands s = true → s ∈ candidates) ∧
    candidates.length = {out['suffix_count']} ∧ ({extra_claim}) := by
  exact ⟨atomicMeasure_probability _ _ weights_valid weights_sum,
    ⟨enclosure.1, enclosure.2.1.trans enclosure.2.2⟩,
    selected_le _ weights (fractions witness) weights_valid (fractions_valid witness),
    witness_suffix, enclosure.2.1, enclosure.2.2, menu_valid.1, menu_valid.2.1, complete_menu,
    menu_valid.2.2, {extra_proof}⟩
#print axioms certified_value
"""
    if len(source.encode("utf-8")) > dc.MAX_SOURCE_BYTES:
        raise VerificationError("Generated proof exceeds the source-size limit.")
    return source


def verify(expected: Request, certificate: Any, *, lean_dir: Path, timeout: float = 240) -> dict:
    """Accept only a closed kernel proof bound to the exact caller request/output.

    At most six atoms, 64 suffixes and the shared source-size/timeout limits are
    supported. Some correct producer outputs may need stronger proof witnesses
    than this generator supplies; failure never becomes a verified result.
    """
    snapshot = _snapshot(expected, certificate)
    source = proof_source(expected, snapshot)
    if type(timeout) not in (int, float) or not 0 < timeout <= 600:
        raise VerificationError("Timeout must lie in (0,600] seconds.")
    try:
        run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=lean_dir, input=source,
                             text=True, encoding="utf-8", capture_output=True, timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise VerificationError("Kernel execution unavailable or verification resource limit reached.") from exc
    report = run.stdout+run.stderr
    try:
        dc.validate_kernel_report(report, run.returncode, sqrt=False)
    except VerificationError as exc:
        exc.kernel_report = report
        raise
    return dict(verified=True, request=expected.as_dict(), output=snapshot["output"], menu=snapshot["menu"],
                proof_source=source, proof_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                kernel_report=report, scope="bounded_global_selection_output_not_statistical_risk",
                global_enclosure_verified=True, exact_optimum_verified=snapshot["output"].get("optimality_proved", False),
                relative_approximation_verified=expected.operation == "approximate",
                python_execution_verified=False, internal_solver_trace_verified=False,
                polynomial_verification_cost_verified=False, external_compiled_cache_trusted=True)
