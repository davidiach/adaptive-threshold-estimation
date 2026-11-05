"""A paid, sign-neutral pilot for a supplied finite family of gap laws.

The true law must be one of the candidates. This does not test that premise
or provide adaptation over arbitrary unknown laws. The statistical argument
is in docs/FINITE_FAMILY_ADAPTATION.md; Python execution is not Lean-verified.
"""

from dataclasses import dataclass
from fractions import Fraction
from random import Random

from .budget_ladders import CoinFactory, _budget
from .rare_event_functional import FiniteGapLaw, Rational, rational


@dataclass(frozen=True)
class LawPilotPlan:
    candidates: tuple[FiniteGapLaw, ...]
    delta: Fraction
    signatures: tuple[tuple[Fraction, ...], ...]
    separation: Fraction
    samples_per_moment: int

    @property
    def moments(self) -> int:
        return len(self.signatures[0])

    @property
    def flip_cap(self) -> int:
        return self.samples_per_moment * self.moments * (self.moments + 1)


@dataclass(frozen=True)
class LawPilotResult:
    selected: int
    observed: tuple[Fraction, ...]
    flips: int
    items: int


def plan_law_pilot(candidates, *, delta: Rational, max_moments: int = 32) -> LawPilotPlan:
    """Compute exact moment signatures and a deterministic physical flip cap.

    Increasing max_moments can distinguish more difficult candidate families.
    Duplicate laws are rejected. A singleton family requires no flips.
    """
    laws = tuple(candidates)
    if not laws or any(not isinstance(law, FiniteGapLaw) for law in laws):
        raise ValueError("Supply a nonempty family of FiniteGapLaw candidates.")
    if len(set(laws)) != len(laws):
        raise ValueError("Candidate laws must be distinct.")
    failure = rational(delta)
    if not 0 < failure < 1:
        raise ValueError("delta must lie strictly between zero and one.")
    if type(max_moments) is not int or max_moments < 1:
        raise ValueError("max_moments must be a positive integer.")
    if len(laws) == 1:
        return LawPilotPlan(laws, failure, ((),), Fraction(0), 0)
    signatures = [[] for _ in laws]
    support_size = len({atom.gap for law in laws for atom in law.atoms})
    for k in range(1, min(support_size - 1, max_moments) + 1):
        for law, row in zip(laws, signatures):
            row.append(sum(atom.mass * (2 * atom.gap) ** (2 * k) for atom in law.atoms))
        rows = tuple(tuple(row) for row in signatures)
        if len(set(rows)) == len(laws):
            separation = min(
                max(abs(a - b) for a, b in zip(rows[i], rows[j]))
                for i in range(len(laws)) for j in range(i)
            )
            # L >= log2(2m/delta) >= log(2m/delta), without floating point.
            inverse = Fraction(2 * k, 1) / failure
            ceiling = -(-inverse.numerator // inverse.denominator)
            exponent = (ceiling - 1).bit_length()
            required = 32 * exponent / separation**2
            samples = -(-required.numerator // required.denominator)
            return LawPilotPlan(laws, failure, rows, separation, samples)
    raise ValueError("Moment limit does not separate these candidates; increase max_moments.")


def run_law_pilot(plan: LawPilotPlan, coin_factory: CoinFactory, *,
                  budget: int, seed: int = 0) -> LawPilotResult:
    """Identify the candidate using only fresh coins and their paid flips.

    Refuses insufficient authorization before creating any coin. Callers must
    use fresh independent coins and randomness for subsequent estimation.
    """
    allowance = _budget(budget)
    if not isinstance(plan, LawPilotPlan):
        raise TypeError("Expected a LawPilotPlan.")
    expected = plan_law_pilot(plan.candidates, delta=plan.delta,
                             max_moments=max(1, plan.moments))
    if plan != expected:
        raise ValueError("Pilot plan does not match its candidate laws and failure allowance.")
    if allowance < plan.flip_cap:
        raise ValueError(f"Pilot requires authorization for {plan.flip_cap} flips.")
    rng = Random(seed)
    observed = []
    items = flips = 0
    for k in range(1, plan.moments + 1):
        total = 0
        for _ in range(plan.samples_per_moment):
            flip = coin_factory(rng)
            items += 1
            parity = 1
            for _ in range(2 * k):
                bit = flip()
                flips += 1
                if type(bit) is not int or bit not in (0, 1):
                    raise ValueError("A flip callback must return the integer 0 or 1.")
                parity *= 2 * bit - 1
            total += parity
        observed.append(Fraction(total, plan.samples_per_moment))
    tolerance = plan.separation / 4
    compatible = [
        i for i, row in enumerate(plan.signatures)
        if all(abs(x - a) <= tolerance for x, a in zip(observed, row))
    ]
    # On the proved good event the compatible candidate exists and is unique.
    # On a failure path the total, deterministic fallback is candidate zero.
    selected = compatible[0] if compatible else 0
    return LawPilotResult(selected, tuple(observed), flips, items)

