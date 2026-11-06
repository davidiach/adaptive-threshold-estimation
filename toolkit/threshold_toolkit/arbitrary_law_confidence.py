"""An observable oracle-adaptive confidence ladder for arbitrary positive gap laws.

The mathematical argument is a paper proof in docs/ARBITRARY_LAW_ADAPTATION.md.
This implementation and its PRNG are not Lean-verified. Its radius comes from
the selected executable plan's MSE certificate, not a claimed sharp constant.
"""

from fractions import Fraction as F

from .budget_ladders import CoinFactory, Exact, _budget, _exact
from .confidence_ladders import ClosedInterval, ConfidenceLadder
from .gap_envelope import _relay, gap_envelope_program, plan_gap_envelope
from .known_law_confidence import known_law_interval


def arbitrary_law_interval(*, rho: Exact, cap: int, delta: Exact, rng):
    """Learn a conservative law, then use fresh coins for its confidence stage."""
    rarity, failure = _exact(rho), _exact(delta)
    _budget(cap)
    if not 0 < rarity <= F(1, 4) or not 0 < failure <= F(1, 4):
        raise ValueError("Require rho and delta in (0,1/4].")
    selected = None
    depth = 1
    while True:
        candidate = plan_gap_envelope(depth, rho=rarity, delta=failure / 2)
        if candidate.flip_cap > cap // 2:
            break
        selected = candidate
        depth += 1
    if selected is None:
        return ClosedInterval(0, rarity)
    envelope = yield from gap_envelope_program(selected)
    # Pilot labels are below this bound even when probes terminate early.
    offset = selected.blocks * sum(b + 1 for b in selected.probe_caps)
    continuation = known_law_interval(
        envelope, rho=rarity, cap=cap - selected.flip_cap, delta=failure / 2, rng=rng)
    return (yield from _relay(continuation, offset))


def arbitrary_law_confidence(coin_factory: CoinFactory, *, rho: Exact, delta: Exact,
                             seed: int = 0) -> ConfidenceLadder:
    """Return nested intervals with cumulative physical caps, using flips alone.

    Fresh coins must be independent, with conditionally iid persistent flips.
    The gap law is arbitrary on (0,1/2], and the total positive fraction is at
    most rho; signs may depend on gaps. No candidate laws or integrals enter.
    """
    rarity = _exact(rho)
    if not 0 < rarity <= F(1, 4):
        raise ValueError("rho must lie in (0,1/4].")

    def stage(cap, failure, rng):
        return arbitrary_law_interval(rho=rarity, cap=cap, delta=failure, rng=rng)

    return ConfidenceLadder(stage, coin_factory, delta=delta, upper=rarity, seed=seed)
