"""Kernel-checked certificates for the exact toolkit's numerical primitives.

``produce`` alone makes NO verification claim. ``verify`` elaborates a proof
about the caller's expected request and the supplied output using the pinned
Lean project. Python, serialization, process launch and source/cache identity
remain explicit execution boundaries. See docs/DETERMINISTIC_VERIFICATION.md.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import hashlib
from pathlib import Path
import re
import subprocess
from typing import Any

from .rare_event_functional import (
    Interval, Precision, cost_entropy, log_interval, sqrt_interval,
)

SCHEMA = "ate-kernel-numerics-v1"
MAX_INPUT_BITS = 2048
MAX_ENDPOINT_BITS = 8192
MAX_COSTS = 16
MAX_SOURCE_BYTES = 2_000_000
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class VerificationError(ValueError):
    """No verified result was produced (invalid data, failed proof or resource limit)."""


def _exact(value: Any, bits: int = MAX_INPUT_BITS) -> Fraction:
    if type(value) not in (int, str, Fraction):
        raise VerificationError("Expected an exact int, string or Fraction; no float/bool.")
    # Bound text before parsing, including decimal/exponent strings.
    if isinstance(value, str) and (len(value) > 2*bits or not re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", value)):
        raise VerificationError("Use a bounded integer or numerator/denominator string.")
    try:
        q = Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise VerificationError("Invalid rational.") from exc
    if max(q.numerator.bit_length(), q.denominator.bit_length()) > bits:
        raise VerificationError("Rational exceeds the certificate resource limit.")
    return q


@dataclass(frozen=True)
class Request:
    operation: str
    values: tuple[Fraction, ...]
    bits: int = 80
    log_terms: int = 32

    def __post_init__(self) -> None:
        if self.operation not in ("sqrt", "log", "entropy"):
            raise VerificationError("Supported operations: sqrt, log, entropy.")
        if type(self.values) is not tuple or len(self.values) > MAX_COSTS:
            raise VerificationError("Supply at most 16 exact values in a tuple.")
        object.__setattr__(self, "values", tuple(_exact(v) for v in self.values))
        try:
            Precision(self.bits, self.log_terms)
        except ValueError as exc:
            raise VerificationError(str(exc)) from exc
        if self.operation != "entropy" and len(self.values) != 1:
            raise VerificationError("sqrt/log require exactly one argument.")
        if any(v < 0 for v in self.values) or (self.operation == "log" and self.values[0] == 0):
            raise VerificationError("Nonnegative inputs required; log requires a positive input.")

    def as_dict(self) -> dict[str, Any]:
        return dict(operation=self.operation, values=[str(v) for v in self.values],
                    bits=self.bits, log_terms=self.log_terms)


def produce(request: Request) -> dict[str, Any]:
    """Call the existing toolkit; the returned data are still untrusted."""
    if request.operation == "sqrt":
        result = sqrt_interval(request.values[0], request.bits)
    elif request.operation == "log":
        result = log_interval(request.values[0], request.log_terms)
    else:
        result = cost_entropy(request.values, Precision(request.bits, request.log_terms))
    for endpoint in (result.lower, result.upper):
        _exact(endpoint, MAX_ENDPOINT_BITS)
    return dict(schema=SCHEMA, request=request.as_dict(), output=result.as_dict())


def _output(request: Request, certificate: Any) -> Interval:
    if type(certificate) is not dict or set(certificate) != {"schema", "request", "output"}:
        raise VerificationError("Unexpected certificate fields.")
    if certificate["schema"] != SCHEMA:
        raise VerificationError("Unknown schema.")
    # Python equality alone accepts True == 1. Check the JSON data types before
    # comparing the canonical request, including list rather than tuple values.
    bound = certificate["request"]
    if (type(bound) is not dict or set(bound) != {"operation", "values", "bits", "log_terms"}
            or type(bound["operation"]) is not str or type(bound["values"]) is not list
            or any(type(v) is not str for v in bound["values"])
            or type(bound["bits"]) is not int or type(bound["log_terms"]) is not int):
        raise VerificationError("Malformed request binding.")
    if bound != request.as_dict():
        raise VerificationError("Certificate does not match the caller's expected request.")
    out = certificate["output"]
    if type(out) is not dict or set(out) != {"lower", "upper"}:
        raise VerificationError("Expected exactly lower and upper endpoints.")
    if any(type(out[k]) is not str for k in out):
        raise VerificationError("Endpoints must be exact rational strings.")
    lo, hi = (_exact(out[k], MAX_ENDPOINT_BITS) for k in ("lower", "upper"))
    if lo > hi:
        raise VerificationError("Reversed output interval.")
    return Interval(lo, hi)


def _q(x: Fraction) -> str:
    _exact(x, MAX_ENDPOINT_BITS)
    return f"({x.numerator}/{x.denominator}:ℚ)"


def _interval(x: Interval) -> str:
    return f"⟨{_q(x.lower)}, {_q(x.upper)}⟩"


def _point(q: Fraction) -> str:
    return f"(.leaf {_interval(Interval(q, q))})"


def _exponent(x: Fraction) -> int:
    k = x.numerator.bit_length()-x.denominator.bit_length()
    return k-1 if x < Fraction(2)**k else k


def _log_evidence(x: Fraction, output: Interval, terms: int) -> str:
    # This witness is independently checked with a looser, proved geometric
    # remainder. Extra terms make it fit inside the legacy tighter enclosure.
    witness = f"⟨{_exponent(x)}, {terms+8}⟩"
    return f"(.logarithm {_interval(output)} {witness} {witness} {_point(x)})"


def _entropy_evidence(request: Request, output: Interval) -> str:
    total = sum(request.values, Fraction(0))
    tail = Interval(Fraction(0), Fraction(0))
    evidence = _point(Fraction(0))
    for a in reversed(request.values):
        if a == 0:
            term, child = Interval(Fraction(0), Fraction(0)), _point(Fraction(0))
        else:
            logarithm = log_interval(total/a, request.log_terms)
            term = logarithm.scale(a)
            child = f"(.unary {_interval(term)} {_log_evidence(total/a, logarithm, request.log_terms)})"
        tail = term+tail
        evidence = f"(.binary {_interval(tail)} {child} {evidence})"
    return f"(.binary {_interval(output)} {_point(total)} {evidence})"


_REDUCE = """accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ"""


def proof_source(expected: Request, certificate: Any) -> str:
    """Emit a closed theorem about expected inputs, never certificate-supplied code.

    Emitting source is not acceptance. Call verify, or independently run and
    audit this source in the pinned Lean environment.
    """
    out = _output(expected, certificate)
    claimed = _interval(out)
    if expected.operation == "entropy":
        vector = "!["+", ".join(_q(v) for v in expected.values)+"]"
        vector = f"({vector} : Fin {len(expected.values)} → ℚ)"
        target = f"ThresholdHC.EntropyTailQuantile.costEntropy (fun i => ({vector} i : ℝ))"
        evidence = _entropy_evidence(expected, out)
        proof = f"apply entropy_accepted_sound {vector} (by norm_num [Fin.forall_fin_succ]) (c := {evidence})"
    else:
        x = expected.values[0]
        target = f"Real.{expected.operation} ({_q(x)}:ℝ)"
        evidence = (f"(.unary {claimed} {_point(x)})" if expected.operation == "sqrt"
                    else _log_evidence(x, out, expected.log_terms))
        proof = f"apply accepted_sound (e := .{expected.operation} (.rational {_q(x)})) (c := {evidence})"
    source = f"""import ThresholdHC.DeterministicCertificates.Entropy
open ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
theorem certified_value : Contains {claimed} ({target}) := by
  {proof}
  norm_num [{_REDUCE}]
#print axioms certified_value
"""
    if expected.operation == "sqrt":
        # Verify the advertised relative/absolute width as well as enclosure.
        source += f"""theorem certified_precision :
    ({_q(out.upper)}:ℝ) - ({_q(out.lower)}:ℝ) ≤ ({_q(Fraction(1, 2**expected.bits))}:ℝ) *
      min 1 (Real.sqrt ({_q(expected.values[0])}:ℝ)) := by
  apply sqrtPrecisionCheck_sound (output := {claimed})
  · norm_num [sqrtPrecisionCheck]
  · norm_num
#print axioms certified_precision
"""
    if len(source.encode("utf-8")) > MAX_SOURCE_BYTES:
        raise VerificationError("Generated proof exceeds the source-size limit.")
    return source


def validate_kernel_report(report: str, returncode: int, *, sqrt: bool) -> None:
    """Require exactly the named closed proofs and only the allowed axioms."""
    if returncode or re.search(r"\bsorry\b|\berror:", report):
        raise VerificationError("Lean rejected the certificate proof.")
    found: dict[str, set[str]] = {}
    for name, axioms in re.findall(r"'?(certified_value|certified_precision)'? depends on axioms: \[([^]]*)\]", report):
        if name in found:
            raise VerificationError("Duplicate kernel report.")
        found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for name in re.findall(r"'?(certified_value|certified_precision)'? does not depend on any axioms", report):
        if name in found:
            raise VerificationError("Duplicate kernel report.")
        found[name] = set()
    required = {"certified_value", "certified_precision"} if sqrt else {"certified_value"}
    if set(found) != required or any(not a <= ALLOWED_AXIOMS for a in found.values()):
        raise VerificationError("Missing proof or forbidden transitive axiom.")


def verify(expected: Request, certificate: Any, *, lean_dir: Path,
           timeout: float = 120) -> dict[str, Any]:
    """Accept only after the kernel checks enclosure and (for sqrt) precision.

    Requires a current build of DeterministicCertificates.Entropy. Timeout,
    unavailable Lean, exhausted precision/resources, and all malformed inputs
    raise VerificationError. There is no Python-only fallback to success.
    """
    # Keep the returned endpoints identical to those proved, even if a caller
    # mutates its original certificate while the kernel subprocess is running.
    output = _output(expected, certificate).as_dict()
    snapshot = dict(schema=SCHEMA, request=expected.as_dict(), output=output)
    source = proof_source(expected, snapshot)
    if type(timeout) not in (int, float) or not 0 < timeout <= 600:
        raise VerificationError("Timeout must lie in (0,600] seconds.")
    try:
        run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=lean_dir,
                             input=source, text=True, encoding="utf-8", capture_output=True,
                             timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise VerificationError("Kernel execution unavailable or verification resource limit reached.") from exc
    report = run.stdout+run.stderr
    try:
        validate_kernel_report(report, run.returncode, sqrt=expected.operation == "sqrt")
    except VerificationError as exc:
        exc.kernel_report = report
        raise
    return dict(verified=True, request=expected.as_dict(), output=output,
                proof_source=source, kernel_report=report,
                proof_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                scope="numerical_enclosure_and_sqrt_precision_not_statistical_risk",
                python_execution_verified=False, external_compiled_cache_trusted=True)
