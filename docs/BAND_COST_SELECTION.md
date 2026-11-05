# Finite-law selection with repeated band costs

The [finite-law suffix theorem](../results/bandwise-suffix-20261104/README.md)
gives a sufficient family of $\prod_j(n_j+1)$ selections for a law with $n_j$
atoms in band $j$. For many occupied bands this family may be too large to
enumerate. When possible suffix costs repeat across bands, the following
reduction can be much smaller.

**Theorem.** Suppose $m$ dyadic bands are occupied. For each band and each
nonempty upper-gap suffix form its inverse-square cost
$a=\sum_{i\text{ selected}} w_i/d_i^2$. Let $r$ be the number of distinct
positive values of $a$ across all menus. It suffices to evaluate at most
$\binom{m+r}{r}$ terminal states. Each state retains one actual selection.
For fixed $r$, both the number of states and the number of transitions are
polynomial in the number of atoms and bands.

**Proof.** After processing $j$ bands, group partial selections by the
multiset of their positive costs. The entropy price for a *completed*
selection is symmetric in those costs. In fact, with $A=\sum a$, it is
$G=\sum a(1+\log(A/a))$. Extending two partial selections with the same
multiset by identical choices in the remaining bands therefore gives the
same rare term $\sqrt{\rho G/B}$.

Retain a partial selection that saves the most ordinary cost in each group.
Each common extension saves the same additional amount, so the retained
selection is at least as good after every extension. The empty prefix starts
the induction. Trying all suffix options of the next band maintains it.
Clipping the final objective at $\rho$ preserves the ordering. The suffix
theorem supplies an optimizer over all submeasures, so the terminal
minimum equals the original selection functional $K$.

A multiset has $r$ nonnegative multiplicities summing to at most $j$.
There are at most $\binom{j+r}{r}$ such vectors. For a fixed band order the
number of transitions is bounded by
$\sum_{j=1}^m(n_j+1)\binom{j-1+r}{r}$. The actual reachable state count can
be smaller. If almost every cost is distinct, the worst case is still
exponential.

## Exact comparisons inside the search

An atom's ordinary cost is $w_i$ when $B d_i^2\le1$ and
$w_i/(d_i\sqrt B)$ otherwise. Thus each saved cost is $x+y/\sqrt B$ for
rational $x,y$ on rational input. To compare two costs subtract their
coefficients. If the signs oppose, compare $B x^2$ with $y^2$ in the direction
determined by the sign of $x$. This decides the ordering, including ties,
without rounding or computing a logarithm.

Only the terminal comparisons require enclosures for logs and square roots.
The minimum of all lower endpoints and the minimum of all upper endpoints
enclose $K$. The solver returns a witness with the latter upper endpoint.
If its upper bound is at most all competing lower bounds, it certifies a
global minimizer of the clipped objective. Otherwise the enclosure and
feasible witness are still valid. Increasing the precision can separate
near ties. Lean now checks the mathematical finite-menu compression,
optimality induction, state and transition bounds, exact saving comparison,
and endpoint certificate rules in a [14-statement audit](../results/band-cost-formal-20261105/README.md).
The prerequisite suffix theorem is separately Lean-checked.

The formal solver uses one tag for the empty option, so a length-$j$ trace
has $j$ tags including zeros. Ignoring zeros recovers the positive-cost
multiset; zero costs contribute no entropy. Thus $r$ positive tags plus the
zero tag give the stated weak-composition bound. The recursion processes the
tail of the menu list first; reversing the band's menu list represents any
chosen processing order.

This audit verifies the finite-menu algorithm, not the Python code or its
construction of menus from a measure. The identification of those concrete
menus with $K$ remains a paper argument. In particular, formal verification
of the reduction does not settle the polynomial-time question for
unrestricted distinct costs.

## Example with 64 occupied bands

With the toolkit on the Python path, take $d_i=2^{-i}$ and masses
proportional to $d_i^2$ for $i=1,\ldots,64$. Every nonempty suffix has the
same cost. The following example checks 4,160 transitions and 65 terminal
states and certifies that selecting the two largest gaps attains $K$.

```python
from fractions import Fraction as F
from threshold_toolkit.band_cost_selection import select_by_band_cost
from threshold_toolkit.rare_event_functional import FiniteGapLaw

gaps = [F(1, 2**i) for i in range(1, 65)]
z = sum(d*d for d in gaps)
law = FiniteGapLaw([(d, d*d/z) for d in gaps])
result = select_by_band_cost(law, rho="1/4", budget=2**32)
assert result.suffix_count == 2**64
assert result.final_states == 65 and result.transitions == 4160
assert result.optimality_proved
assert [a.gap for a, keep in zip(law.atoms, result.selected) if keep] == [F(1,4), F(1,2)]
```

The transition limit raises an error before expanding a stage that would
exceed the allowance. The bound on state counts counts arithmetic operations
separately from the bit cost and the precision of transcendental evaluations.
