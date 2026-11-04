"""Inputs to the observable rare-event estimator of v6 Appendix D.

The oracle describes the known *magnitude* law. Neither the planner nor the
classifier receives the gap or sign of an individual coin. Integrals use the
quantile core sigma (retaining the appropriate fraction at the boundary).
Split its complement into tau on B*d² >= 1 and zeta on B*d² < 1.
"""
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Mapping, Protocol

from .rare_event_functional import FiniteGapLaw, Interval, Precision, band_index, log_interval, quantile_split

F = Fraction


@dataclass(frozen=True)
class SplitIntegrals:
    """Certified upper bounds at one (rho, B), including all occupied core bands.

    band_costs[j] bounds integral_sigma,j d^-2. unresolved_mass bounds zeta's
    mass, and tail_inverse bounds integral_tau d^-1. For a positive cap M,
    resolved_error(M) bounds integral_(sigma+tau) min(1,(M*d²)^-2);
    tail_work(M) bounds integral_tau min(M,17*d^-2*(1+log_+(M*d²))).
    Upper bounds may be conservative. resolved_error must tend to zero.
    """
    band_costs: Mapping[int, F]
    unresolved_mass: F
    tail_inverse: F
    resolved_error: Callable[[int], F]
    tail_work: Callable[[int], F]


class KnownGapOracle(Protocol):
    def split(self, rho: F, budget: F, precision: Precision) -> SplitIntegrals:
        """Return certified design integrals under the caller's known law."""
        ...

    def null_prefix(self, heads: int, tails: int, tolerance: F) -> Interval:
        """Enclose integral (1/2-d)^heads * (1/2+d)^tails to absolute width <= tolerance."""
        ...


@dataclass(frozen=True)
class FiniteGapOracle:
    """Adapter for a finite rational magnitude law, including atoms at the split."""
    law: FiniteGapLaw

    def null_prefix(self, heads: int, tails: int, tolerance: F) -> Interval:
        value = sum((a.mass * (F(1,2)-a.gap)**heads * (F(1,2)+a.gap)**tails
                     for a in self.law.atoms), F(0))
        return Interval(value, value)

    def split(self, rho: F, budget: F, precision: Precision) -> SplitIntegrals:
        core, _ = quantile_split(self.law, rho)
        bands = {}
        resolved = []
        ordinary = []
        z = H = F(0)
        for atom, fraction in zip(self.law.atoms, core):
            d = atom.gap
            selected = atom.mass * fraction
            residual = atom.mass - selected
            if selected:
                j = band_index(d)
                bands[j] = bands.get(j, F(0)) + selected/d**2
            if budget*d*d >= 1:
                if residual:
                    ordinary.append((d, residual))
                    H += residual/d
                resolved.append((d, atom.mass))
            else:
                z += residual
                if selected:
                    resolved.append((d, selected))

        def error(cap: int) -> F:
            return sum((w * min(1, 1/(cap*d*d)**2) for d,w in resolved), F(0))

        def work(cap: int) -> F:
            total = F(0)
            for d,w in ordinary:
                x = cap*d*d
                if x <= 1:
                    total += w*cap
                else:
                    total += w*min(cap, 17*(1+log_interval(x, precision.log_terms).upper)/d**2)
            return total

        return SplitIntegrals(bands, z, H, error, work)
