"""Paid finite-family identification followed by known-law confidence stages.

The true gap law must belong to the supplied family; this controller does not
test membership or adapt over arbitrary laws. Its intervals use executable
MSE certificates, not the exact constant of the noncomputable Lean theorem.
"""

from dataclasses import dataclass
from fractions import Fraction
from random import Random
from threading import Lock

from .budget_ladders import CoinFactory, Exact, _budget, _exact, _exclusive_advance
from .confidence_ladders import ClosedInterval, ConfidenceState
from .known_law_confidence import known_law_ladder
from .known_law_oracle import FiniteGapOracle
from .law_identification import LawPilot, LawPilotState, plan_law_pilot


@dataclass(frozen=True)
class FiniteFamilyState:
    authorized_budget: int
    reserved_budget: int
    flips: int
    interval: ClosedInterval
    pilot: LawPilotState
    continuation: ConfidenceState | None

    @property
    def selected(self) -> int | None:
        return None if self.pilot.result is None else self.pilot.result.selected


class FiniteFamilyConfidenceLadder:
    """One persistent confidence sequence, charged to a cumulative flip budget.

    Half of delta is assigned to identification and half to the continuation.
    During the pilot the interval is [0,rho]. After identification, only fresh
    coins are created; pilot coins are never handed to an estimation stage.
    Factories must supply iid persistent coins and conditionally iid flips.
    The physical cap applies also when identification fails. Python execution,
    PRNG independence and oracle-rate constants are not formally verified.
    Overlapping advance_to calls, including callback re-entry, are rejected.
    """

    def __init__(self, candidates, coin_factory: CoinFactory, *, rho: Exact,
                 delta: Exact, max_moments: int = 32, seed: int = 0):
        self.rho, self.delta = _exact(rho), _exact(delta)
        if not 0 < self.rho <= Fraction(1, 4) or not 0 < self.delta <= Fraction(1, 4):
            raise ValueError("rho and delta must lie in (0,1/4].")
        if type(seed) is not int:
            raise TypeError("seed must be an integer.")
        self.plan = plan_law_pilot(candidates, delta=self.delta / 2,
                                   max_moments=max_moments)
        root = Random(seed)
        self._pilot = LawPilot(self.plan, coin_factory, seed=root.getrandbits(256))
        self._continuation_seed = root.getrandbits(256)
        self._coins = coin_factory
        self._ladder = None
        self._authorized = 0
        self._failed = False
        self._advance_lock = Lock()

    @_exclusive_advance
    def advance_to(self, total_budget: int) -> FiniteFamilyState:
        allowance = _budget(total_budget)
        if self._failed:
            raise RuntimeError("A callback failed; this confidence sequence is invalidated.")
        if allowance < self._authorized:
            raise ValueError("Cumulative authorized budget cannot decrease.")
        self._authorized = allowance
        try:
            pilot = self._pilot.advance_to(min(allowance, self.plan.flip_cap))
            continuation = None
            interval = ClosedInterval(0, self.rho)
            flips = reserved = pilot.flips
            if pilot.result is not None:
                if self._ladder is None:
                    law = FiniteGapOracle(self.plan.candidates[pilot.result.selected])
                    self._ladder = known_law_ladder(
                        law, self._coins, rho=self.rho, delta=self.delta / 2,
                        seed=self._continuation_seed)
                continuation = self._ladder.advance_to(allowance - self.plan.flip_cap)
                interval = continuation.interval
                flips += continuation.flips
                reserved += continuation.reserved_budget
        except BaseException:
            self._failed = True
            raise
        assert flips <= reserved <= allowance
        return FiniteFamilyState(allowance, reserved, flips, interval, pilot, continuation)
