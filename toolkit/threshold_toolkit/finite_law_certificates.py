"""Closed Lean certificates for finite-law objectives and oracle integrals.

The legacy producer is untrusted. Only ``verify`` accepts a result, after the
kernel checks a theorem bound to the caller's exact canonical request.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess
from typing import Any

from . import deterministic_certificates as dc
from .known_law_oracle import FiniteGapOracle
from .rare_event_functional import (
    FiniteGapLaw, Interval, Precision, band_index, cost_entropy,
    evaluate_selection, log_interval, quantile_split, sqrt_interval,
)

VerificationError = dc.VerificationError
SCHEMA = "ate-kernel-finite-law-v1"
MAX_ATOMS = 16
MAX_BAND = 256


@dataclass(frozen=True)
class Request:
    operation: str
    atoms: tuple[tuple[F, F], ...]
    selected: tuple[F, ...] = ()
    rho: F = F(1, 4)
    budget: F = F(16)
    cap: int = 16
    heads: int = 0
    tails: int = 0
    bits: int = 80
    log_terms: int = 32

    def __post_init__(self) -> None:
        if type(self.operation) is not str or self.operation not in ("objective", "oracle", "prefix"):
            raise VerificationError("Supported operations: objective, oracle, prefix.")
        if type(self.atoms) is not tuple or not 1 <= len(self.atoms) <= MAX_ATOMS:
            raise VerificationError("Supply 1 to 16 canonical atoms in a tuple.")
        if any(type(a) is not tuple or len(a) != 2 for a in self.atoms):
            raise VerificationError("Each atom must be a (gap, mass) tuple.")
        atoms = tuple(tuple(dc._exact(x) for x in a) for a in self.atoms)
        if (any(not 0 < d <= F(1, 2) or w <= 0 for d, w in atoms)
                or sum(w for _, w in atoms) != 1
                or any(a[0] >= b[0] for a, b in zip(atoms, atoms[1:]))):
            raise VerificationError("Require increasing distinct positive gaps, positive masses summing to one.")
        if any(band_index(d) > MAX_BAND for d, _ in atoms):
            raise VerificationError("Band index exceeds the verification resource limit.")
        object.__setattr__(self, "atoms", atoms)
        if type(self.selected) is not tuple:
            raise VerificationError("Selected fractions must be a tuple.")
        selected = tuple(dc._exact(x) for x in self.selected)
        if self.operation == "objective":
            if len(selected) != len(atoms) or any(not 0 <= x <= 1 for x in selected):
                raise VerificationError("One selected fraction in [0,1] per atom is required.")
        elif selected:
            raise VerificationError("Oracle core fractions are outputs, not caller assumptions.")
        object.__setattr__(self, "selected", selected)
        for name in ("rho", "budget"):
            object.__setattr__(self, name, dc._exact(getattr(self, name)))
        if not 0 < self.rho <= F(1, 4) or self.budget <= 0:
            raise VerificationError("Require 0 < rho <= 1/4 and budget > 0.")
        for name, low, high in (("cap", 1, 10**9), ("heads", 0, 128), ("tails", 0, 128)):
            x = getattr(self, name)
            if type(x) is not int or not low <= x <= high:
                raise VerificationError(f"{name} is outside its integer verification range.")
        try:
            Precision(self.bits, self.log_terms)
        except ValueError as exc:
            raise VerificationError(str(exc)) from exc

    def as_dict(self) -> dict[str, Any]:
        return dict(operation=self.operation, atoms=[[str(d), str(w)] for d, w in self.atoms],
                    selected=[str(s) for s in self.selected], rho=str(self.rho), budget=str(self.budget),
                    cap=self.cap, heads=self.heads, tails=self.tails, bits=self.bits, log_terms=self.log_terms)


def produce(request: Request) -> dict[str, Any]:
    """Call the unchanged finite toolkit. No verification is implied."""
    law = FiniteGapLaw(request.atoms)
    precision = Precision(request.bits, request.log_terms)
    oracle = FiniteGapOracle(law)
    if request.operation == "objective":
        out = evaluate_selection(law, request.selected, rho=request.rho,
                                 budget=request.budget, precision=precision).as_dict()
    elif request.operation == "prefix":
        out = oracle.null_prefix(request.heads, request.tails, F(1, 2**request.bits)).as_dict()
    else:
        core, threshold = quantile_split(law, request.rho)
        split = oracle.split(request.rho, request.budget, precision)
        out = dict(core=[str(s) for s in core], threshold=str(threshold),
                   band_costs={str(j): str(a) for j, a in split.band_costs.items()},
                   unresolved_mass=str(split.unresolved_mass), tail_inverse=str(split.tail_inverse),
                   resolved_error=str(split.resolved_error(request.cap)), tail_work=str(split.tail_work(request.cap)))
    certificate = dict(schema=SCHEMA, request=request.as_dict(), output=out)
    _output(request, certificate)
    return certificate


def _output(request: Request, certificate: Any) -> dict:
    if type(certificate) is not dict or set(certificate) != {"schema", "request", "output"}:
        raise VerificationError("Unexpected certificate fields.")
    if type(certificate["schema"]) is not str or certificate["schema"] != SCHEMA:
        raise VerificationError("Unknown schema.")
    # Exact recursive types matter: True == 1 is not a valid request binding.
    def same(a: Any, b: Any) -> bool:
        if type(a) is not type(b):
            return False
        if type(b) is dict:
            return a.keys() == b.keys() and all(same(a[k], v) for k, v in b.items())
        if type(b) is list:
            return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
        return a == b
    if not same(certificate["request"], request.as_dict()):
        raise VerificationError("Certificate does not match the caller's expected request.")
    out = certificate["output"]
    fields = ({"lower", "upper"} if request.operation != "oracle" else
              {"core", "threshold", "band_costs", "unresolved_mass", "tail_inverse", "resolved_error", "tail_work"})
    if type(out) is not dict or set(out) != fields:
        raise VerificationError("Unexpected output fields.")
    def number(x: Any) -> str:
        if type(x) is not str:
            raise VerificationError("Output numbers must be exact rational strings.")
        return str(dc._exact(x, dc.MAX_ENDPOINT_BITS))
    if request.operation != "oracle":
        result = {k: number(out[k]) for k in ("lower", "upper")}
        if F(result["lower"]) > F(result["upper"]):
            raise VerificationError("Reversed output interval.")
        return result
    if type(out["core"]) is not list or len(out["core"]) != len(request.atoms):
        raise VerificationError("Expected one core fraction per atom.")
    bands = out["band_costs"]
    allowed = {str(band_index(d)) for d, _ in request.atoms}
    if type(bands) is not dict or any(type(k) is not str or k not in allowed for k in bands):
        raise VerificationError("Unknown or malformed band label.")
    return dict(core=[number(s) for s in out["core"]],
                band_costs={k: number(v) for k, v in bands.items()},
                **{k: number(out[k]) for k in fields - {"core", "band_costs"}})


def _vec(xs, kind="ℚ") -> str:
    xs = tuple(xs)
    values = [dc._q(x) if kind == "ℚ" else str(x) for x in xs]
    return f"(![{', '.join(values)}] : Fin {len(xs)} → {kind})"


def _binary(output: Interval, left: str, right: str) -> str:
    return f"(.binary {dc._interval(output)} {left} {right})"


def _unary(output: Interval, child: str) -> str:
    return f"(.unary {dc._interval(output)} {child})"


def _sum(children: list[tuple[Interval, str]]) -> tuple[Interval, str]:
    total, evidence = Interval(F(0), F(0)), dc._point(F(0))
    for value, child in reversed(children):
        total = value + total
        evidence = _binary(total, child, evidence)
    return total, evidence


def _objective_evidence(r: Request, out: Interval, labels: tuple[int, ...]) -> str:
    costs = tuple(sum((w*s/d**2 for (d, w), s in zip(r.atoms, r.selected)
                       if band_index(d) == j), F(0)) for j in labels)
    req = dc.Request("entropy", costs, r.bits, r.log_terms)
    entropy = cost_entropy(costs, Precision(r.bits, r.log_terms))
    scaled = entropy.scale(r.rho/r.budget)
    rare = Interval(sqrt_interval(scaled.lower, r.bits).lower, sqrt_interval(scaled.upper, r.bits).upper)
    re = _unary(rare, _unary(scaled, dc._entropy_evidence(req, entropy)))
    children = []
    for (d, w), s in zip(r.atoms, r.selected):
        x = 1/(r.budget*d*d)
        root = sqrt_interval(x, r.bits)
        capped = root.cap(F(1))
        value = capped.scale(w*(1-s))
        children.append((value, _unary(value, _binary(capped, dc._point(F(1)),
                                                     _unary(root, dc._point(x))))))
    total, rest = _sum(children)
    return _binary(out, dc._point(r.rho), _binary(rare+total, re, rest))


def _work_evidence(r: Request, core: tuple[F, ...], upper: F) -> str:
    children = []
    for (d, w), s in zip(r.atoms, core):
        v = w*(1-s) if r.budget*d*d >= 1 else F(0)
        x = F(r.cap)*d*d
        log = log_interval(x, r.log_terms)
        positive = Interval(max(F(0), log.lower), max(F(0), log.upper))
        added = positive + Interval(F(1), F(1))
        scaled = added.scale(17/d**2)
        capped = scaled.cap(F(r.cap))
        value = capped.scale(v)
        ev = _binary(positive, dc._point(F(0)), dc._log_evidence(x, log, r.log_terms))
        ev = _binary(added, dc._point(F(1)), ev)
        ev = _binary(capped, dc._point(F(r.cap)), _unary(scaled, ev))
        children.append((value, _unary(value, ev)))
    total, evidence = _sum(children)
    # The root sum bounds may be widened to [0, actual legacy upper bound].
    # Preserve the checked child tree; accepted checks the new root numerically.
    if not children:
        return dc._point(F(0))
    _, tail = _sum(children[1:])
    return _binary(Interval(F(0), upper), children[0][1], tail)


_REDUCE = dc._REDUCE + ", objectiveExpr, costs, inBand, imin, imax, tailWorkExpr, tailWeights"


def proof_source(expected: Request, certificate: Any) -> str:
    """Emit a closed measure-level theorem. Source generation is not acceptance."""
    out = _output(expected, certificate)
    r = expected
    g, w = _vec(d for d, _ in r.atoms), _vec(w for _, w in r.atoms)
    labels = tuple(sorted({band_index(d) for d, _ in r.atoms}))
    js = _vec(labels, "ℕ")
    rho, budget = dc._q(r.rho), dc._q(r.budget)
    common = f"""import ThresholdHC.FiniteLawCertificates.Oracles
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.FiniteLawCertificates ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
private def gaps := {g}
private def weights := {w}
private def labels := {js}
private theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem weights_valid : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private theorem weights_sum : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
private noncomputable def law := atomicMeasure (points gaps gaps_valid) weights
"""
    if r.operation == "prefix":
        claimed = dc._interval(Interval(F(out["lower"]), F(out["upper"])))
        body = f"""theorem certified_value : IsProbabilityMeasure law ∧
    Contains {claimed} (nullPrefixIntegral law {r.heads} {r.tails}) ∧
    ({dc._q(F(out['upper']))}:ℝ)-({dc._q(F(out['lower']))}:ℝ) ≤ ({dc._q(F(1,2**r.bits))}:ℝ) := by
  refine ⟨atomicMeasure_probability _ _ weights_valid weights_sum, ?_, ?_⟩
  · rw [law, nullPrefix_eq gaps weights gaps_valid weights_valid]
    norm_num [Contains, nullPrefixValue, gaps, weights, Fin.sum_univ_succ]
  · norm_num
"""
    elif r.operation == "objective":
        selected = _vec(r.selected)
        claimed = dc._interval(Interval(F(out["lower"]), F(out["upper"])))
        evidence = _objective_evidence(r, Interval(F(out["lower"]), F(out["upper"])), labels)
        body = f"""private def selected := {selected}
private theorem selected_valid : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1 := by
  norm_num [selected, Fin.forall_fin_succ]
private theorem labels_injective : Function.Injective labels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [labels] at *
private theorem bands_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true := by
  norm_num [gaps, labels, inBand, Fin.forall_fin_succ, Fin.exists_fin_succ]
theorem certified_value : IsProbabilityMeasure law ∧
    atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i) ≤ law ∧
    Contains {claimed} (min (ENNReal.ofReal ({rho}:ℝ))
      (ThresholdHC.EntropyTail.selectionObjective law ({rho}:ℝ) ({budget}:ℝ)
        (atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i)))).toReal ∧
    (ThresholdHC.EntropyTail.selection law ({rho}:ℝ) ({budget}:ℝ)).toReal ≤ ({dc._q(F(out['upper']))}:ℝ) := by
  have hc : accepted (objectiveExpr gaps weights selected labels {rho} {budget}) {claimed}
      {evidence} = true := by
    norm_num [gaps, weights, selected, labels, {_REDUCE}]
  exact ⟨atomicMeasure_probability _ _ weights_valid weights_sum,
    selected_le _ weights selected weights_valid selected_valid,
    objective_accepted_sound gaps weights selected labels {rho} {budget} gaps_valid weights_valid
      selected_valid (by norm_num) (by norm_num) labels_injective bands_cover hc,
    selection_upper gaps weights selected labels {rho} {budget} gaps_valid weights_valid
      selected_valid (by norm_num) (by norm_num) labels_injective bands_cover hc⟩
"""
    else:
        body = _oracle_proof(r, out, labels)
    source = common + body + "#print axioms certified_value\n"
    if len(source.encode("utf-8")) > dc.MAX_SOURCE_BYTES:
        raise VerificationError("Generated proof exceeds the source-size limit.")
    return source


def _oracle_proof(r: Request, out: dict, labels: tuple[int, ...]) -> str:
    core = tuple(F(x) for x in out["core"])
    t = F(out["threshold"])
    boundary_mass = sum((w for d, w in r.atoms if d == t), F(0))
    if not boundary_mass:
        raise VerificationError("The proposed quantile threshold is not an atom.")
    fraction = (r.rho-sum((w for d, w in r.atoms if d < t), F(0)))/boundary_mass
    rho, budget, cap = dc._q(r.rho), dc._q(r.budget), dc._q(F(r.cap))
    band_values = _vec(F(out["band_costs"].get(str(j), "0")) for j in labels)
    claimed = dc._interval(Interval(F(0), F(out["tail_work"])))
    evidence = _work_evidence(r, core, F(out["tail_work"]))
    reduce = "gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ"
    return f"""private def selected := {_vec(core)}
private theorem selected_valid : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1 := by
  norm_num [selected, Fin.forall_fin_succ]
private theorem selected_weights_valid (i) : 0 ≤ weights i*selected i :=
  mul_nonneg (weights_valid i) (selected_valid i).1
private noncomputable def core := ThresholdHC.EntropyTailQuantile.quantileCore law ({rho}:ℝ)
private noncomputable def tail := (law-core).restrict {{x : ThresholdHC.Tier6.Gap | 1 ≤ ({budget}:ℝ)*(x:ℝ)^2}}
private noncomputable def unresolved := (law-core).restrict {{x : ThresholdHC.Tier6.Gap | ({budget}:ℝ)*(x:ℝ)^2 < 1}}
private theorem core_eq : core = atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i) := by
  apply quantileCore_atomic (points gaps gaps_valid) weights selected weights_valid weights_sum
    (ρ := ({rho}:ℝ)) (t := ({dc._q(t)}:ℝ)) (by norm_num) (by norm_num)
    {dc._q(fraction)} (by norm_num)
  all_goals norm_num [{reduce}]
private theorem tail_eq : tail = atomicMeasure (points gaps gaps_valid)
    (tailWeights gaps weights selected {budget}) := by
  rw [tail, core_eq]
  exact tailMeasure_eq gaps weights selected {budget} gaps_valid weights_valid selected_valid
private theorem unresolved_eq : unresolved = atomicMeasure (points gaps gaps_valid)
    (unresolvedWeights gaps weights selected {budget}) := by
  rw [unresolved, core_eq]
  exact unresolvedMeasure_eq gaps weights selected {budget} gaps_valid weights_valid selected_valid
private theorem resolved_eq : core+tail = atomicMeasure (points gaps gaps_valid)
    (resolvedWeights gaps weights selected {budget}) := by
  rw [tail, core_eq]
  exact resolvedMeasure_eq gaps weights selected {budget} gaps_valid weights_valid selected_valid
theorem certified_value : IsProbabilityMeasure law ∧
    ThresholdHC.EntropyTailQuantile.quantileThreshold law ({rho}:ℝ) = ({dc._q(t)}:ℝ) ∧
    core = atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i) ∧
    (∀ j, ThresholdHC.EntropyTail.bandCost core (labels j) = ENNReal.ofReal ({band_values} j:ℝ)) ∧
    unresolved.real Set.univ = ({dc._q(F(out['unresolved_mass']))}:ℝ) ∧
    (∫ x : ThresholdHC.Tier6.Gap, (x:ℝ)⁻¹ ∂tail) = ({dc._q(F(out['tail_inverse']))}:ℝ) ∧
    (∫ x : ThresholdHC.Tier6.Gap, min 1 (1/(({cap}:ℝ)*(x:ℝ)^2)^2) ∂(core+tail)) =
      ({dc._q(F(out['resolved_error']))}:ℝ) ∧
    Contains {claimed} (tailWorkIntegral tail ({cap}:ℝ)) := by
  refine ⟨atomicMeasure_probability _ _ weights_valid weights_sum, ?_, core_eq, ?_, ?_, ?_, ?_, ?_⟩
  · let : IsProbabilityMeasure law := atomicMeasure_probability (points gaps gaps_valid) weights weights_valid weights_sum
    apply quantileThreshold_eq_of_mass law (ρ := ({rho}:ℝ)) (by norm_num) (by norm_num)
    all_goals rw [law, atomicMeasure_real _ _ weights_valid]
    all_goals norm_num [{reduce}]
  · intro j
    rw [core_eq, bandCost_atomic _ _ selected_weights_valid]
    norm_num [labels, ThresholdHC.EntropyTail.band, {reduce}]
    fin_cases j <;> norm_num [labels, {reduce}]
  · rw [unresolved_eq, atomicMeasure_real _ _ (by norm_num [unresolvedWeights, {reduce}])]
    norm_num [unresolvedWeights, {reduce}]
  · rw [tail_eq, inverseIntegral_eq gaps _ gaps_valid
      (tailWeights_nonneg gaps weights selected {budget} weights_valid selected_valid)]
    norm_num [inverseValue, tailWeights, {reduce}]
  · rw [resolved_eq, errorIntegral_eq gaps _ {cap} gaps_valid (by
      intro i
      exact add_nonneg (selected_weights_valid i)
        (tailWeights_nonneg gaps weights selected {budget} weights_valid selected_valid i))]
    norm_num [errorValue, resolvedWeights, tailWeights, {reduce}]
  · rw [tail_eq]
    apply tailWork_accepted_sound gaps _ {cap} gaps_valid
      (tailWeights_nonneg gaps weights selected {budget} weights_valid selected_valid) (c := {evidence})
    norm_num [{reduce}, {_REDUCE}]
"""


def verify(expected: Request, certificate: Any, *, lean_dir: Path, timeout: float = 180) -> dict:
    """Accept only the exact supplied output after the kernel checks its theorem."""
    output = _output(expected, certificate)
    source = proof_source(expected, dict(schema=SCHEMA, request=expected.as_dict(), output=output))
    if type(timeout) not in (int, float) or not 0 < timeout <= 600:
        raise VerificationError("Timeout must lie in (0,600] seconds.")
    try:
        run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=lean_dir, input=source,
                             text=True, encoding="utf-8", capture_output=True, timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise VerificationError("Kernel execution unavailable or verification resource limit reached.") from exc
    report = run.stdout + run.stderr
    try:
        dc.validate_kernel_report(report, run.returncode, sqrt=False)
    except VerificationError as exc:
        exc.kernel_report = report
        raise
    return dict(verified=True, request=expected.as_dict(), output=output, proof_source=source,
                kernel_report=report, proof_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                scope="finite_law_measure_objective_oracle_certificate_not_statistical_risk",
                global_optimum_verified=False, python_execution_verified=False,
                external_compiled_cache_trusted=True)
