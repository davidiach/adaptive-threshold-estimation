"""Finite-law selection by grouping suffix choices with the same entropy cost."""

from bisect import bisect_left
from dataclasses import dataclass
from fractions import Fraction as F

from .rare_event_functional import (
    FiniteGapLaw,
    Interval,
    Precision,
    Rational,
    _parameters,
    band_index,
    cost_entropy,
    sqrt_interval,
)


@dataclass(frozen=True)
class SelectionResult:
    value: Interval
    selected: tuple[bool, ...]
    optimality_proved: bool
    suffix_count: int
    final_states: int
    transitions: int


@dataclass(frozen=True)
class _Choice:
    fixed: F
    scaled: F
    count: int
    parent: "_Choice | None"


def _saves_more(x: F, y: F, budget: F) -> bool:
    """Test x + y/sqrt(budget) > 0 with rational arithmetic, including ties."""
    if not x:
        return y > 0
    if not y:
        return x > 0
    if (x > 0) == (y > 0):
        return x > 0
    difference = budget * x * x - y * y
    return difference > 0 if x > 0 else difference < 0


def select_by_band_cost(
    law: FiniteGapLaw,
    *,
    rho: Rational,
    budget: Rational,
    precision: Precision = Precision(),
    max_transitions: int = 200_000,
) -> SelectionResult:
    """Enclose the global minimum and recover a feasible bandwise selection.

    The result certifies an optimizer when its upper endpoint separates it
    from the lower bounds on every competing cost multiset. Ambiguous
    endpoint comparisons can be tightened by increasing precision.
    Repeated suffix costs reduce the search; max_transitions limits work
    on unstructured inputs. Raising this limit never changes the answer.
    """
    r, b = _parameters(rho, budget)
    if type(max_transitions) is not int or max_transitions < 1:
        raise ValueError("max_transitions must be a positive integer")
    by_band: dict[int, list[int]] = {}
    for i, atom in enumerate(law.atoms):
        by_band.setdefault(band_index(atom.gap), []).append(i)
    bands = list(by_band.values())
    # A state key is the sorted multiset of positive suffix cost IDs.
    # The cost of an empty suffix is zero and contributes no entropy.
    costs: dict[F, int] = {}
    frontier: dict[tuple[int, ...], _Choice] = {(): _Choice(F(0), F(0), 0, None)}
    total_fixed = total_scaled = F(0)
    transitions = 0
    suffix_count = 1
    for group in bands:
        next_count = len(group) + 1
        transitions += len(frontier) * next_count
        if transitions > max_transitions:
            raise ValueError("Selection search exceeds max_transitions")
        suffix_count *= next_count
        options = [(None, F(0), F(0))]
        cost = fixed = scaled = F(0)
        for i in reversed(group):
            atom = law.atoms[i]
            cost += atom.mass / atom.gap**2
            if b * atom.gap**2 <= 1:
                fixed += atom.mass
            else:
                scaled += atom.mass / atom.gap
            options.append((costs.setdefault(cost, len(costs)), fixed, scaled))
        total_fixed += fixed
        total_scaled += scaled
        following: dict[tuple[int, ...], _Choice] = {}
        for key, prior in frontier.items():
            for count, (cost_id, fixed, scaled) in enumerate(options):
                new_key = key
                if cost_id is not None:
                    at = bisect_left(key, cost_id)
                    new_key = key[:at] + (cost_id,) + key[at:]
                saved_fixed = prior.fixed + fixed
                saved_scaled = prior.scaled + scaled
                old = following.get(new_key)
                if old is None or _saves_more(
                    saved_fixed - old.fixed, saved_scaled - old.scaled, b
                ):
                    following[new_key] = _Choice(
                        saved_fixed, saved_scaled, count, prior
                    )
        frontier = following

    by_id = list(costs)
    scale = sqrt_interval(1 / b, precision.bits)
    values = []
    for key, choice in frontier.items():
        g = cost_entropy((by_id[i] for i in key), precision)
        rare = Interval(
            sqrt_interval(r * g.lower / b, precision.bits).lower,
            sqrt_interval(r * g.upper / b, precision.bits).upper,
        )
        fixed = total_fixed - choice.fixed
        tail = Interval(fixed, fixed) + scale.scale(total_scaled - choice.scaled)
        values.append(((rare + tail).cap(r), choice))
    best = min(range(len(values)), key=lambda i: values[i][0].upper)
    top, path = values[best]
    lower = min(v.lower for v, _ in values)
    certified = all(
        i == best or top.upper <= v.lower for i, (v, _) in enumerate(values)
    )
    selected = [False] * len(law.atoms)
    for group in reversed(bands):
        for i in group[len(group) - path.count :]:
            selected[i] = True
        path = path.parent
    return SelectionResult(
        Interval(lower, top.upper),
        tuple(selected),
        certified,
        suffix_count,
        len(values),
        transitions,
    )
