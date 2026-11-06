# Prescribed-accuracy selection for arbitrary finite laws

This package gives a paper proof and implementation of a `(1+epsilon)`
approximation to the deterministic entropy-tail functional `K`, with an
actual bandwise-suffix witness. The mathematical scheme is polynomial in
binary input length and `1/epsilon`, even when all positive band costs differ.
The exact polynomial-time question remains open.

* [Contract and baseline ledger](CONTRACT.md)
* [Full proof, state bound, bit complexity, and prior art](NOTE.md)
* [Rational-arithmetic implementation](../../toolkit/threshold_toolkit/approximate_selection.py)
* [Independent-formula subset tests](../../toolkit/tests/test_approximate_selection.py)
* [Reproduction script](reproduce.py)
* [Lean entropy and compression components](../../lean/ThresholdHC/SelectionApproximation/README.md)
* [Exact-type and transitive-axiom record](../../results/selection-approximation-20261106/README.md)

## Use

With `toolkit` on the Python path:

```python
from threshold_toolkit.rare_event_functional import FiniteGapLaw
from threshold_toolkit.approximate_selection import select_approximately

law = FiniteGapLaw([("1/2", "1/2"), ("1/32", "1/2")])
result = select_approximately(law, rho="1/4", budget=10000, epsilon="1/10")
print(result.value)     # lower <= K <= witness objective <= upper
print(result.selected)  # mask in law.atoms order
assert result.value.upper <= (1+result.epsilon)*result.value.lower
```

The guarantee concerns the **capped rate functional**, not statistical risk.
The endpoints are exact rationals, conditional on the paper proof and the
existing formal suffix theorem. The implementation has a transition limit and
the toolkit's interval-precision limits. It raises if it cannot meet the
requested tolerance within those limits. It does not certify exact optimality.

## Measured example

Take 64 gaps `d_i=2^(-i)` and masses proportional to
`d_i^2 (1+(i-1)/10^12)`, for `i=1,...,64`. The 64 positive menu costs are all
distinct. At `rho=1/4`, `B=2^32`, and `epsilon=1/10`, the run retains 128 final
states after 4,160 transitions, out of `2^64 = 18,446,744,073,709,551,616`
possible suffix traces. Its witness selects gaps `1/4` and `1/2`. The global
endpoint ratio is approximately 1.025, within the requested 1.1.

This is a deliberately near-equal-cost example demonstrating compression
where exact cost equality is unavailable. It is not a claim that all 64-band
instances have this state count or that the method is practically faster
on every law. The worst-case polynomial bound has substantial constants.

## Verification performed

From this worktree's root:

```sh
python -m unittest discover -s toolkit/tests -p 'test_approximate_selection.py' -v
python -m unittest discover -s toolkit/tests -v
python tools/freeze.py --verify
git -c core.whitespace=cr-at-eol diff --check
python research/2026-11-06-selection-approximation/reproduce.py
python tools/verify_selection_approximation.py
python -m unittest discover -s tools -p 'test_selection_approximation.py' -v
```

The eight new tests passed. They include 24 seeded small random laws checked
against **every hard subset** using a separately written 90-digit Decimal
formula; point laws, saturation and tiny positive values; real compression
on distinct costs; exact bin boundaries; logarithm enclosures; automatic final
precision refinement; and rejection of invalid inputs or insufficient resources.
All 285 toolkit tests passed. Frozen-source verification passed.
The reproduction script creates a fresh directory under
`.runtime/selection-approximation/` and binds its examples to source hashes.
Decimal is an adversarial numerical cross-check, not a formal proof checker.

The new Lean development proves the actual-entropy perturbation bound and the
feasible state-compression invariant for certified bins. Its exact-type and
transitive-axiom audit rebuilds all six local modules. It also checks the
relative entropy corollary, surrogate bounds, zero case and bin-cell geometry
as supporting declarations. The full FPTAS and Python execution remain outside
that formal scope. The proof and implementation were self-reviewed in one
agent session; no independent agent review, specialist review, or CI result
is claimed. Original frozen specifications, dependency pins, published evidence
and manuscripts remain unchanged; the new components have a separate lock.

## Research decisions and rejected shortcuts

1. **Use the current boundary.** The general-law minimax problem in the old
   continuation prompt was already formalized. We selected the unresolved
   many-cost computation problem instead.
2. **Aim for prescribed accuracy.** Exact efficient optimization remains
   unresolved. This contract explicitly targets arbitrary relative accuracy;
   it does not silently claim to resolve exact optimization.
3. **Total cost alone is insufficient.** The vectors `(1,0,...,0)` and
   `(1/m,...,1/m)` have the same total cost but entropies `1` and `1+log(m)`.
   Grouping only by total cost cannot preserve relative entropy uniformly.
4. **Control cancellation explicitly.** The two additive summaries are not
   themselves the entropy. The derivative bound and `G>=A` in (4) of the
   note are needed to justify their subtraction.
5. **Use rational bin boundaries.** Dyadic subdivision provides the same
   multiplicative bound as a geometric grid without huge rational powers.
6. **Keep proof and numerical status separate.** The surrogate perturbation
   lemma and trimming invariant are now formally checked. Their composition
   with certified concrete bins, the already formal menu theorem, parameter
   bounds and rational endpoint evaluation remains to be formalized. Passing
   numerical tests does not complete those steps.

The general method draws on established approximation algorithms. The limited
prior-art check and precise project-specific contribution are in the note.
No claim of external novelty is made.
