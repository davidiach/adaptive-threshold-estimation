"""A paid, sign-neutral pilot for a supplied finite family of gap laws.

The true law must be one of the candidates. This does not test that premise
or provide adaptation over arbitrary unknown laws. The statistical argument
is in docs/FINITE_FAMILY_ADAPTATION.md; Python execution is not Lean-verified.
"""

from dataclasses import dataclass
from fractions import Fraction
from random import Random
from threading import Lock

from .budget_ladders import CoinFactory, _budget, _exclusive_advance
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
        return 2 * self.samples_per_moment * self.moments


@dataclass(frozen=True)
class LawPilotResult:
    selected: int
    observed: tuple[Fraction, ...]
    flips: int
    items: int


@dataclass(frozen=True)
class LawPilotState:
    authorized_budget: int
    flips: int
    items: int
    result: LawPilotResult | None


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


def _validate_plan(plan: LawPilotPlan) -> None:
    if not isinstance(plan, LawPilotPlan):
        raise TypeError("Expected a LawPilotPlan.")
    expected = plan_law_pilot(plan.candidates, delta=plan.delta,
                             max_moments=max(1, plan.moments))
    if plan != expected:
        raise ValueError("Pilot plan does not match its candidate laws and failure allowance.")


class LawPilot:
    """A persistent pilot that can pause after any paid flip.

    advance_to authorizes a cumulative budget. The same coin and prefix parity
    survive pauses; repeated calls at the same budget perform no extra work.
    Exceptions from callbacks invalidate the pilot so it cannot be resumed.
    Overlapping advance_to calls, including callback re-entry, are rejected.
    """

    def __init__(self, plan: LawPilotPlan, coin_factory: CoinFactory, *, seed: int = 0):
        _validate_plan(plan)
        if not callable(coin_factory):
            raise TypeError("coin_factory must be callable.")
        if type(seed) is not int:
            raise TypeError("seed must be an integer.")
        self.plan = plan
        self._factory, self._rng = coin_factory, Random(seed)
        self._authorized = self._flips = self._items = self._prefix = 0
        self._parity = 1
        self._totals = [0] * plan.moments
        self._coin = None
        self._failed = False
        self._advance_lock = Lock()
        self._result = LawPilotResult(0, (), 0, 0) if not plan.flip_cap else None

    @_exclusive_advance
    def advance_to(self, total_budget: int) -> LawPilotState:
        allowance = _budget(total_budget)
        if self._failed:
            raise RuntimeError("A callback failed; this pilot is invalidated.")
        if allowance < self._authorized:
            raise ValueError("Cumulative authorized budget cannot decrease.")
        self._authorized = allowance
        try:
            while self._flips < min(allowance, self.plan.flip_cap):
                if self._coin is None:
                    self._coin = self._factory(self._rng)
                    if not callable(self._coin):
                        raise TypeError("coin_factory must return a callable.")
                    self._items += 1
                self._flips += 1
                bit = self._coin()
                if type(bit) is not int or bit not in (0, 1):
                    raise ValueError("A flip callback must return the integer 0 or 1.")
                self._prefix += 1
                self._parity *= 2 * bit - 1
                if self._prefix % 2 == 0:
                    self._totals[self._prefix // 2 - 1] += self._parity
                if self._prefix == 2 * self.plan.moments:
                    self._coin = None
                    self._prefix, self._parity = 0, 1
            if self._result is None and self._flips == self.plan.flip_cap:
                observed = tuple(Fraction(x, self.plan.samples_per_moment)
                                 for x in self._totals)
                tolerance = self.plan.separation / 4
                compatible = [
                    i for i, row in enumerate(self.plan.signatures)
                    if all(abs(x - a) <= tolerance for x, a in zip(observed, row))
                ]
                # On the good event the true candidate is uniquely compatible.
                self._result = LawPilotResult(compatible[0] if compatible else 0,
                                              observed, self._flips, self._items)
        except BaseException:
            self._failed = True
            raise
        return LawPilotState(allowance, self._flips, self._items, self._result)


def run_law_pilot(plan: LawPilotPlan, coin_factory: CoinFactory, *,
                  budget: int, seed: int = 0) -> LawPilotResult:
    """Complete the pilot, refusing an insufficient budget before sampling.

    Use LawPilot instead to pause and resume. Subsequent estimation must use
    fresh independent coins and private randomness.
    """
    allowance = _budget(budget)
    pilot = LawPilot(plan, coin_factory, seed=seed)
    if allowance < plan.flip_cap:
        raise ValueError(f"Pilot requires authorization for {plan.flip_cap} flips.")
    result = pilot.advance_to(allowance).result
    assert result is not None
    return result

