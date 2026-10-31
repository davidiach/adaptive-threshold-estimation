"""Certified finite-law evaluation of the entropy-tail *rate functional*.

This is NOT an estimator, a confidence interval, or a certified statistical
risk. The rational enclosures certify numerical evaluations conditional on
the deterministic lemmas in the accompanying research note. No floating-point
arithmetic is used in any bound. Inputs are exact integers, decimal/rational
strings, or Fraction objects; floats are deliberately rejected.

Developed against repository commit 6ad675e04570cc1ef6bece8e26beb81e1a176471;
see research/2026-10-30-certified-selection/. Apache-2.0.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import isqrt, prod
from typing import Iterable, Mapping, Sequence, Union
import hashlib
import json

Rational = Union[int, str, Fraction]
SCOPE = "deterministic_entropy_tail_functional_not_statistical_risk"
# v2 drops v1's fixed base_commit field, which misdated certificates made by later code.
SCHEMA = "ate-rare-functional-v2"
ZERO = Fraction(0)
ONE = Fraction(1)


def rational(value: Rational) -> Fraction:
    """Parse an exact rational without silently accepting a binary float."""
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise TypeError("Use int, Fraction, or a decimal/rational string; not float/bool.")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"Invalid exact rational: {value!r}") from exc
    if max(result.numerator.bit_length(), result.denominator.bit_length()) > 16384:
        raise ValueError("Rational exceeds the 16384-bit input safety limit.")
    return result


@dataclass(frozen=True)
class Interval:
    lower: Fraction
    upper: Fraction

    def __post_init__(self) -> None:
        if not isinstance(self.lower, Fraction) or not isinstance(self.upper, Fraction):
            raise TypeError("Interval endpoints must be Fractions.")
        if self.lower > self.upper:
            raise ValueError("Reversed interval.")

    @property
    def width(self) -> Fraction:
        return self.upper - self.lower

    def __add__(self, other: Interval) -> Interval:
        return Interval(self.lower + other.lower, self.upper + other.upper)

    def scale(self, x: Fraction) -> Interval:
        if x < 0:
            return Interval(x * self.upper, x * self.lower)
        return Interval(x * self.lower, x * self.upper)

    def cap(self, x: Fraction) -> Interval:
        return Interval(min(x, self.lower), min(x, self.upper))

    def as_dict(self) -> dict[str, str]:
        return {"lower": str(self.lower), "upper": str(self.upper)}


@dataclass(frozen=True)
class Precision:
    bits: int = 80
    log_terms: int = 32

    def __post_init__(self) -> None:
        if type(self.bits) is not int or not 16 <= self.bits <= 512:
            raise ValueError("bits must be an integer in [16,512].")
        if type(self.log_terms) is not int or not 4 <= self.log_terms <= 256:
            raise ValueError("log_terms must be an integer in [4,256].")


def _floor_log2(x: Fraction) -> int:
    if x <= 0:
        raise ValueError("Positive rational required.")
    n, d = x.numerator, x.denominator
    k = n.bit_length() - d.bit_length()
    too_large = n < (d << k) if k >= 0 else (n << -k) < d
    return k - 1 if too_large else k


@lru_cache(maxsize=8192)
def sqrt_interval(x: Fraction, bits: int = 80) -> Interval:
    """Enclose sqrt(x) in a dyadic interval of width at most 2**(-bits)*min(1, sqrt(x)).

    Below 1 the grid is refined with the magnitude of x, so tiny values keep
    `bits` relative bits instead of collapsing to [0, 2**(-bits)].
    """
    if not isinstance(x, Fraction):
        raise TypeError("sqrt_interval expects a Fraction.")
    if x < 0 or type(bits) is not int or not 16 <= bits <= 512:
        raise ValueError("Need x>=0 and integer bits in [16,512].")
    # x >= 2**e gives sqrt(x) >= 2**(e/2), so 2**(-shift) <= 2**(-bits)*sqrt(x).
    shift = bits + (max(0, (1 - _floor_log2(x)) // 2) if x else 0)
    k = isqrt((x.numerator << (2 * shift)) // x.denominator)
    lo = Fraction(k, 1 << shift)
    hi = lo if lo * lo == x else Fraction(k + 1, 1 << shift)
    return Interval(lo, hi)


def _log_unit_interval(x: Fraction, terms: int) -> Interval:
    """atanh series for 1<=x<=2; a positive geometric tail bounds the rest."""
    z = (x - 1) / (x + 1)
    z2 = z * z
    power = z
    total = ZERO
    for n in range(terms):
        total += power / (2 * n + 1)
        power *= z2
    lo = 2 * total
    remainder = 2 * power / ((2 * terms + 1) * (1 - z2))
    return Interval(lo, lo + remainder)


@lru_cache(maxsize=8192)
def log_interval(x: Fraction, terms: int = 32) -> Interval:
    """Enclose natural log(x) using rational arithmetic and binary reduction."""
    if not isinstance(x, Fraction):
        raise TypeError("log_interval expects a Fraction.")
    if x <= 0 or type(terms) is not int or not 4 <= terms <= 256:
        raise ValueError("Need x>0 and integer terms in [4,256].")
    if x < 1:
        v = log_interval(1 / x, terms)
        return Interval(-v.upper, -v.lower)
    k = _floor_log2(x)
    y = x / (1 << k)
    return _log_unit_interval(y, terms) + _log_unit_interval(Fraction(2), terms).scale(Fraction(k))


@dataclass(frozen=True)
class Atom:
    gap: Fraction
    mass: Fraction


@dataclass(frozen=True, init=False)
class FiniteGapLaw:
    atoms: tuple[Atom, ...]

    def __init__(self, atoms: Iterable[tuple[Rational, Rational]]) -> None:
        merged: dict[Fraction, Fraction] = {}
        for pair in atoms:
            if not isinstance(pair, (tuple, list)) or len(pair) != 2:
                raise TypeError("Each atom must be a (gap, mass) pair.")
            d, w = map(rational, pair)
            if not ZERO < d <= Fraction(1, 2):
                raise ValueError("Every gap must lie in (0,1/2].")
            if w <= 0:
                raise ValueError("Every supplied mass must be positive.")
            merged[d] = merged.get(d, ZERO) + w
        if not merged or sum(merged.values(), ZERO) != 1:
            raise ValueError("The masses must sum exactly to 1.")
        object.__setattr__(self, "atoms", tuple(Atom(d, w) for d, w in sorted(merged.items())))

    def canonical(self) -> list[dict[str, str]]:
        return [{"gap": str(a.gap), "mass": str(a.mass)} for a in self.atoms]


def band_index(gap: Rational) -> int:
    d = rational(gap)
    if not ZERO < d <= Fraction(1, 2):
        raise ValueError("Gap must lie in (0,1/2].")
    return _floor_log2(1 / d) - 1


def cost_entropy(costs: Iterable[Fraction], precision: Precision = Precision()) -> Interval:
    """G(a)=A+sum a*log(A/a), including exactly zero coordinates."""
    a = tuple(costs)
    if any(not isinstance(x, Fraction) or x < 0 for x in a):
        raise ValueError("Costs must be nonnegative Fractions.")
    total = sum(a, ZERO)
    answer = Interval(total, total)
    for x in a:
        if x:
            answer += log_interval(total / x, precision.log_terms).scale(x)
    return answer


def _parameters(rho: Rational, budget: Rational) -> tuple[Fraction, Fraction]:
    rho, budget = rational(rho), rational(budget)
    if not ZERO < rho <= Fraction(1, 4):
        raise ValueError("rho must lie in (0,1/4].")
    if budget <= 0:
        raise ValueError("budget must be positive.")
    return rho, budget


def _ordinary(law: FiniteGapLaw, budget: Fraction, p: Precision) -> tuple[Interval, ...]:
    return tuple(sqrt_interval(1 / (budget * a.gap**2), p.bits).cap(ONE).scale(a.mass)
                 for a in law.atoms)


def _sum_intervals(values: Iterable[Interval]) -> Interval:
    result = Interval(ZERO, ZERO)
    for v in values:
        result += v
    return result


def _selection_objective(law: FiniteGapLaw, selected: Sequence[Fraction], rho: Fraction,
                         budget: Fraction, p: Precision,
                         ordinary: Sequence[Interval] | None = None) -> Interval:
    if len(selected) != len(law.atoms) or any(not ZERO <= s <= ONE for s in selected):
        raise ValueError("A selected fraction in [0,1] is required for each atom.")
    if ordinary is None:
        ordinary = _ordinary(law, budget, p)
    costs: dict[int, Fraction] = {}
    for atom, s in zip(law.atoms, selected):
        j = band_index(atom.gap)
        costs[j] = costs.get(j, ZERO) + s * atom.mass / atom.gap**2
    entropy = cost_entropy(costs.values(), p)
    rare = Interval(sqrt_interval(rho * entropy.lower / budget, p.bits).lower,
                    sqrt_interval(rho * entropy.upper / budget, p.bits).upper)
    remainder = _sum_intervals(v.scale(1 - s) for v, s in zip(ordinary, selected))
    return rare + remainder


def evaluate_selection(law: FiniteGapLaw, selected: Sequence[Rational], *, rho: Rational,
                       budget: Rational, precision: Precision = Precision()) -> Interval:
    """Enclose one feasible objective; not necessarily the minimum K."""
    r, b = _parameters(rho, budget)
    return _selection_objective(law, tuple(map(rational, selected)), r, b, precision).cap(r)


def quantile_split(law: FiniteGapLaw, rho: Rational) -> tuple[tuple[Fraction, ...], Fraction]:
    """Return core fractions after removing exactly the smallest-gap mass rho."""
    r, _ = _parameters(rho, ONE)
    left = r
    core: list[Fraction] = []
    t = ZERO
    for atom in law.atoms:
        removed = min(left, atom.mass)
        if removed:
            t = atom.gap
        core.append(1 - removed / atom.mass)
        left -= removed
    if left:
        raise AssertionError("Internal quantile accounting failed.")
    return tuple(core), t


def _instance(law: FiniteGapLaw, rho: Fraction, budget: Fraction) -> dict:
    return {"law": law.canonical(), "rho": str(rho), "budget": str(budget)}


def _hash(value: Mapping) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _certificate(law: FiniteGapLaw, rho: Fraction, budget: Fraction, p: Precision,
                 method: str, interval: Interval, **details) -> dict:
    instance = _instance(law, rho, budget)
    return {"schema": SCHEMA, "scope": SCOPE, "method": method,
            "instance": instance, "instance_sha256": _hash(instance),
            "precision": {"bits": p.bits, "log_terms": p.log_terms},
            "K_interval": interval.as_dict(), "details": details}


def quantile_certificate(law: FiniteGapLaw, *, rho: Rational, budget: Rational,
                         precision: Precision = Precision()) -> dict:
    """Cheap rigorous enclosure using K<=Q<=(8/5)*K and T<=K.

    This constant uses the new paper proof, not a Lean-checked statement.
    No stochastic simulation, estimation, or claim of a polynomial-bit running
    time is involved. Arithmetic cost depends on rational bit complexity.
    """
    r, b = _parameters(rho, budget)
    ordinary = _ordinary(law, b, precision)
    core, t = quantile_split(law, r)
    tail = _sum_intervals(v.scale(1 - s) for v, s in zip(ordinary, core))
    q = _selection_objective(law, core, r, b, precision, ordinary).cap(r)
    omega = _sum_intervals(ordinary).cap(r)
    full = _selection_objective(law, (ONE,) * len(law.atoms), r, b, precision, ordinary).cap(r)
    factor_hi = Fraction(8, 5)
    lower = max(tail.lower, q.lower / factor_hi)
    upper = min(q.upper, omega.upper, full.upper, r)
    # Analytic saturation avoids treating interval roundoff as a real gap.
    if b * t * t <= 1:
        lower = upper = r
    return _certificate(law, r, b, precision, "quantile", Interval(lower, upper),
                        Q_interval=q.as_dict(), tail_interval=tail.as_dict(),
                        quantile_gap=str(t), core_fractions=list(map(str, core)),
                        comparison_constant="8/5")


def suffix_search_size(law: FiniteGapLaw) -> int:
    groups: dict[int, int] = {}
    for a in law.atoms:
        j = band_index(a.gap)
        groups[j] = groups.get(j, 0) + 1
    return prod(n + 1 for n in groups.values())


def exhaustive_certificate(law: FiniteGapLaw, *, rho: Rational, budget: Rational,
                           precision: Precision = Precision(), max_states: int = 100000) -> dict:
    """Enclose the global finite-law minimum by enumerating bandwise suffixes.

    The bandwise-threshold lemma reduces 2**n hard subsets to product(n_j+1).
    This remains exponential when many bands have one atom. A state cap causes
    an explicit exception; partial search is NEVER reported as a certificate.
    The returned interval encloses K; the best witness need not be the unique
    optimizer when rigorous objective intervals overlap.
    """
    r, b = _parameters(rho, budget)
    if type(max_states) is not int or max_states < 1:
        raise ValueError("max_states must be a positive integer.")
    count = suffix_search_size(law)
    if count > max_states:
        raise ValueError(f"Complete suffix search needs {count} states; cap is {max_states}. Use quantile_certificate.")
    groups: dict[int, list[int]] = {}
    for i, a in enumerate(law.atoms):
        groups.setdefault(band_index(a.gap), []).append(i)
    ordered_groups = [groups[j] for j in sorted(groups)]
    ordinary = _ordinary(law, b, precision)
    # Precompute each band's suffix cost and complementary ordinary cost.
    # The exponential loop now visits only the occupied bands, not all atoms.
    group_options = []
    for g in ordered_groups:
        prefixes = [Interval(ZERO, ZERO)]
        for i in g:
            prefixes.append(prefixes[-1] + ordinary[i])
        a = ZERO
        options = [(a, prefixes[-1], 0)]
        for k, i in enumerate(reversed(g), start=1):
            atom = law.atoms[i]
            a += atom.mass / atom.gap**2
            options.append((a, prefixes[len(g)-k], k))
        group_options.append(options)
    lower = upper = r
    best_counts = None
    seen = 0
    for choices in product(*group_options):
        entropy = cost_entropy((choice[0] for choice in choices), precision)
        rare = Interval(sqrt_interval(r * entropy.lower / b, precision.bits).lower,
                        sqrt_interval(r * entropy.upper / b, precision.bits).upper)
        remainder = _sum_intervals(choice[1] for choice in choices)
        value = (rare + remainder).cap(r)
        lower = min(lower, value.lower)
        if value.upper < upper:
            upper = value.upper
            best_counts = tuple(choice[2] for choice in choices)
        seen += 1
    if seen != count:
        raise AssertionError("Incomplete enumeration.")
    witness = None
    if best_counts is not None:
        witness = [ZERO] * len(law.atoms)
        for g, k in zip(ordered_groups, best_counts):
            if k:
                for i in g[-k:]:
                    witness[i] = ONE
    # Keep this exhaustive enclosure independent of the quantile comparison.
    return _certificate(law, r, b, precision, "band_suffix_exhaustive", Interval(lower, upper),
                        states_evaluated=seen, original_subset_count=str(1 << len(law.atoms)),
                        all_states_evaluated=True,
                        best_hard_witness=None if witness is None else list(map(str, witness)),
                        witness_claim="feasible upper bound, not unique optimizer")



def threshold_certificate(law: FiniteGapLaw, *, rho: Rational, budget: Rational,
                          precision: Precision = Precision()) -> dict:
    """Scan n+1 global upper-gap cuts for a feasible, constant-factor solution.

    This scan is NOT globally exact across multiple bands. Its best value V
    satisfies K<=V<=Q<=(8/5)*K: the quantile cut's fractional atom can
    be rounded to one of its two endpoints by concavity. The returned lower
    endpoint comes from the independent quantile bound. There are n+1
    candidate evaluations, each involving at most the number of bands.
    """
    r, b = _parameters(rho, budget)
    ordinary = _ordinary(law, b, precision)
    prefixes = [Interval(ZERO, ZERO)]
    for v in ordinary:
        prefixes.append(prefixes[-1] + v)
    costs: dict[int, Fraction] = {}
    upper = r
    best_k = None
    n = len(law.atoms)
    for k in range(n + 1):
        if k:
            atom = law.atoms[n-k]
            j = band_index(atom.gap)
            costs[j] = costs.get(j, ZERO) + atom.mass / atom.gap**2
        entropy = cost_entropy(costs.values(), precision)
        rare_hi = sqrt_interval(r * entropy.upper / b, precision.bits).upper
        candidate_hi = min(r, rare_hi + prefixes[n-k].upper)
        if candidate_hi < upper:
            upper, best_k = candidate_hi, k
    q = quantile_certificate(law, rho=r, budget=b, precision=precision)
    lower = Fraction(q["K_interval"]["lower"])
    return _certificate(law, r, b, precision, "global_threshold_upper", Interval(lower, upper),
                        states_evaluated=n+1, best_selected_count=best_k,
                        globally_exact=False, comparison_constant="8/5")

def verify_certificate(certificate: object, law: FiniteGapLaw, *, rho: Rational,
                       budget: Rational, max_recheck_states: int = 100000) -> bool:
    """Recompute against caller-supplied expected instance, failing closed.

    Replays ALL required candidates for an exhaustive certificate. This is a
    deterministic recomputation checker, not an independent formal proof of
    the Python implementation or the supporting mathematical lemmas.
    """
    try:
        if type(certificate) is not dict:
            return False
        expected_keys = {"schema", "scope", "method", "instance",
                         "instance_sha256", "precision", "K_interval", "details"}
        if set(certificate) != expected_keys:
            return False
        r, b = _parameters(rho, budget)
        expected_instance = _instance(law, r, b)
        if certificate["instance"] != expected_instance or certificate["instance_sha256"] != _hash(expected_instance):
            return False
        cfg = certificate["precision"]
        if type(cfg) is not dict or set(cfg) != {"bits", "log_terms"}:
            return False
        p = Precision(**cfg)
        if certificate["method"] == "quantile":
            rebuilt = quantile_certificate(law, rho=r, budget=b, precision=p)
        elif certificate["method"] == "global_threshold_upper":
            rebuilt = threshold_certificate(law, rho=r, budget=b, precision=p)
        elif certificate["method"] == "band_suffix_exhaustive":
            rebuilt = exhaustive_certificate(law, rho=r, budget=b, precision=p, max_states=max_recheck_states)
        else:
            return False
        # Canonical serialization preserves type distinctions such as 1 vs true.
        return json.dumps(certificate, sort_keys=True, allow_nan=False) == json.dumps(rebuilt, sort_keys=True, allow_nan=False)
    except (TypeError, ValueError, KeyError, OverflowError, ZeroDivisionError):
        return False


def transfer_enclosure(interval: Interval, *, rounding_factor: Rational = 1,
                       tv_radius: Rational = 0, rho: Rational) -> Interval:
    """Transfer an enclosure AFTER caller establishes the law-approximation premises.

    If TV(mu,mu0)<=eta and mu0 is rounded upward within its ORIGINAL dyadic
    bands by at most factor r to law nu, then
        max(0,K_nu.lower-eta) <= K_mu <= min(rho,r*K_nu.upper+eta).
    This function does NOT verify those premises or infer TV from samples.
    """
    r = rational(rounding_factor)
    eta = rational(tv_radius)
    rarity, _ = _parameters(rho, ONE)
    if r < 1 or not ZERO <= eta <= 1 or interval.lower < 0:
        raise ValueError("Need r>=1, 0<=eta<=1 and a nonnegative input interval.")
    return Interval(max(ZERO, interval.lower - eta), min(rarity, r * interval.upper + eta))


@dataclass(frozen=True)
class RoundedLaw:
    law: FiniteGapLaw
    factor: Fraction
    destinations: tuple[Fraction, ...]


def round_up_within_bands(law: FiniteGapLaw, *, subdivisions: int = 16) -> RoundedLaw:
    """Construct a band-preserving upward grid, and its exact max distortion.

    Every atom stays in its original canonical band; d<=d'<=factor*d and
    factor<=1+1/subdivisions. This is deterministic discretization of a given
    law, NOT estimation of that law from observations.
    """
    if type(subdivisions) is not int or not 1 <= subdivisions <= 1000000:
        raise ValueError("subdivisions must be an integer in [1,1000000].")
    destinations: list[Fraction] = []
    atoms: list[tuple[Fraction, Fraction]] = []
    factor = ONE
    for atom in law.atoms:
        j = band_index(atom.gap)
        lower = Fraction(1, 1 << (j + 2))
        cell = (atom.gap / lower - 1) * subdivisions
        k = -(-cell.numerator // cell.denominator)
        d_new = lower * (1 + Fraction(k, subdivisions))
        if not (atom.gap <= d_new and band_index(d_new) == j):
            raise AssertionError("Rounding left its original dyadic band.")
        factor = max(factor, d_new / atom.gap)
        destinations.append(d_new)
        atoms.append((d_new, atom.mass))
    return RoundedLaw(FiniteGapLaw(atoms), factor, tuple(destinations))
