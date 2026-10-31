# Threshold toolkit

A budget calculator and two ready-to-run estimators for one question:

> **What share of my items succeed more often than not?**

Each item has a hidden success rate, and you learn about an item only by trying
it, with each try costing something. Some examples:

- the share of test questions an AI model answers correctly more often than not
  (an item is a question, a try is one graded answer);
- the share of machines in a batch that fail more often than they work;
- the share of simulated market scenarios in which a portfolio usually loses money.

The research in this repository calls a try a "flip", as in flipping a slightly
unfair coin, and the tool uses the same word.

For a **known finite gap law and a known bound on the positive fraction**, the
[rare-event calculator](#3-compute-the-rare-event-rate-for-a-known-finite-law)
evaluates the paper's quantile rate functional and its inverse. This is a
separate calculation from the two executable estimators below.

## Read this first: what building it showed

The paper proves a method that needs no tuning. It never needs to know how close
your items are to 50/50, and its mathematical guarantee is machine-checked.
In the example below, it was **much less accurate than a simple plan**: try
each item a fixed number of times and take a majority vote per item.

For the ten-item guess used in the examples below:

| | Simple plan | Proven no-tuning method |
|---|---:|---:|
| Typical error at 16,384 flips | 5.9 points | 28 points (simulated) |
| A plan found for a 3-point typical error | 258,153 flips | none confirmed; simulated error first meets it at about 4.2 million flips |

In theory the proven method's error shrinks at the minimax rate as budgets
grow. In this example, the simple plan uses far fewer flips. The calculator
gives you the simple plan's numbers and shows the proven method
beside them. The proven method's real advantage is
robustness: the simple plan is only as good as your guess of how close the items
are to 50/50, while the proven method needs no guess at all.

## Install

Python 3.10 or newer with NumPy and SciPy. Either install it:

```sh
pip install ./toolkit
```

or run from the `toolkit/` folder without installing. The estimators themselves
need only the standard library; NumPy and SciPy are used by the calculator.

## 1. Plan the budget

Tell the calculator roughly what the items' success rates look like. There are
three ways:

- `--rates 0.9,0.8,0.55,0.3` lists guessed rates, one per typical item;
- `--rates-file rates.txt` reads them from a file (commas, spaces or new lines;
  `#` starts a comment);
- `--evenly-spread` means rates anywhere from 0% to 100%, equally likely.

Then give either the flips you can afford (`--budget`) or the accuracy you need
(`--target-error`):

```sh
python -m threshold_toolkit --rates 0.9,0.8,0.7,0.6,0.55,0.52,0.45,0.3,0.2,0.1 --budget 16384
```

```
Your guess: 10 guessed items, 60% of them above 50/50.

At an average budget of 16,384 flips:

  Hard to call: 0% of items are within 0.781 points of 50/50.

  Simple plan: 96 items x 169 flips each, then a majority vote per item
    typical error on your guess: 0.0591 (about 5.9 percentage points)
    at most 0.0713 however these items fall on either side of 50/50

  Proven no-tuning method, simulated 200 times on your guess:
    typical error: 0.277 (about 28 percentage points), give or take 0.012
    at most 0.363 with 95% confidence, given these 200 runs
    flips used: 15,540 on average; 90% of runs used at most 31,091, 99% at most 46,572

  On your guess, the simple plan's typical error is 4.7x smaller.

  Proven limits, over every split of items this close to 50/50 between the two sides:
    difficulty score: 0.0951
    no method can promise a typical error below 0.00149 (difficulty / 64)
    the no-tuning method is proven to stay within 48.7 (difficulty x 512), too loose to be useful here

  Returns on more flips: 4x the budget would cut the difficulty score to 50% of today's.
    (50% is the best case, when every item is far from 50/50.)
```

How to read it:

- **Hard to call** counts items within $B^{-1/2}$ of 50/50. This is the gap
  scale in the theorem's modulus, not a lower bound on misclassification probability.
- **Typical error** is the root-mean-square error: roughly how far off the
  estimate usually is. 0.059 means about 6 percentage points.
- **"at most … however these items fall"** evaluates an analytic bias–variance
  bound using binomial tails (an analytic integral for `--evenly-spread`). The
  evaluation uses floating-point arithmetic and is subject to roundoff; it is
  not a certified interval bound. The formula covers items this close to 50/50,
  whichever side each one is on. You
  could have the sides wrong in your guess and it still holds; only the
  closeness has to be right.
- **The proven method's numbers are simulations** of the actual algorithm on your
  guess. Its budget is an average, so single runs vary; the 90% and 99% figures
  show by how much. The "at most … with 95% confidence" figure is a one-sided
  upper confidence bound on the true typical error at that budget, on your
  guess (a Chernoff bound for squared errors in [0, 1]). It stays well above
  zero even when no simulated run made an error: 200 error-free runs only show
  that the typical error is at most about 0.12. Use `--confidence` to change
  the level.
- **Proven limits** come from the paper's machine-checked theorems. The floor
  says no method of any kind can do better in the worst case over splits of
  your population between the two sides, where any share of the items at each
  closeness to 50/50 may be above it. It is not a floor for a fixed list of
  items whose sides are merely unknown: a single item at 90% or 10% is settled
  far more accurately by flipping it repeatedly. Both limits are
  very loose (a factor of about 30,000 apart), which is why the simulation is
  there.
- **Returns on more flips**: when many items sit near 50/50, extra flips buy
  less.

The calculator searches a 1.25× grid of odd flip counts, so it does not promise
the best plan among all possible counts. With `--target-error 0.03` instead of
`--budget`, it finds the cheapest qualifying plan on that grid, up to $2^{24}$
flips per item. A failed search means no plan was found in that search range;
it is not an impossibility result. The calculator also simulates the
proven method at doubling budgets, giving up at 64 times the simple plan's
flips. It reports a budget as confirmed only when the simulations' upper
confidence bound meets the target. The confidence level holds across every
budget the search could try. Confirming a target t needs at least about
log(K / 0.05) / t² runs, where K counts the budgets the search could try
(doubling from 4 up to its limit). That many suffice when no run makes an
error, and errors in the runs usually raise the number needed: with the default
200 runs and the full default search, only targets above roughly 0.17 can be
confirmed. A shorter search, from a cheap simple plan or a smaller
`--max-budget`, lowers this threshold. When the simulated error meets the target
but the bound does not, the calculator says so rather than recommending that
budget. If `--runs` is below this lower bound, it gives the bound; otherwise it
says that no budget it searched was confirmed and that more runs may confirm
one.

Use `--runs` to change the number of simulated runs (default 200) and `--seed` to
change the simulation's seed. With `--target-error`, `--max-budget` (default
16,777,216) caps the doubling search. Simulation time grows with the budget and
the number of runs, and individual simulations above $2^{32}$ flips (about
4.3 billion) are rejected as too slow. A larger `--max-budget` is allowed if
the search meets the target before attempting a simulation above this limit.

## 2. Run it on your items

Write two small functions. One picks a fresh item at random from your
population, with replacement. The other tries that item once and returns `True`
for a success:

```python
import random
from threshold_toolkit import majority_vote_estimate, estimate_fraction

def new_item():
    question = random.choice(questions)
    return lambda: grade(ask_model(question))   # one try: True or False

# The simple plan, using the numbers the calculator gave you:
share = majority_vote_estimate(new_item, items=96, flips_per_item=169)

# The proven no-tuning method: give it only the average budget.
result = estimate_fraction(new_item, budget=16384)
print(result.estimate, result.flips)
```

If your tries can run in parallel, pass `batched=True`. The function for an item
then takes a number `k` and returns how many of `k` fresh tries succeeded.

`toolkit/examples/quickstart.py` runs the whole flow on simulated questions.

## 3. Compute the rare-event rate for a known finite law

The rare-event model assumes a known law of the magnitudes
$D=|p-1/2|$ and a known global bound $\theta\le\rho\le1/4$ on the
positive fraction. The signs remain unknown. Give the calculator gaps and
relative masses directly:

```sh
python -m threshold_toolkit rare-event --gaps 0.01,0.1,0.4 --weights 1,2,7 --rarity 0.05 --budget 100000
```

This law has masses 0.1, 0.2 and 0.7. Removing the smallest-gap mass
$\rho=0.05$ splits the atom at gap 0.01. The calculation gives:

| Quantity | Value at $B=100{,}000$ |
|---|---:|
| Tail contribution $T_h$ | 0.0158113883 |
| Core entropy contribution $h\sqrt{\rho\Gamma_\kappa}$ | 0.0178107278 |
| Quantile functional $Q(B)$ | 0.0336221161 |
| Comparison interval for the selection functional $\mathcal K(B)$ | [0.0201732697, 0.0336221161] |

The interval comes from the new deterministic paper proof
$3Q/5\le\mathcal K\le Q$ in the
[computation note](../docs/RARE_EVENT_COMPUTATION.md). It improves the
previous comparison factor $1+2\sqrt2$ to $5/3$. The proof applies to every
positive-gap law; the executable calculator accepts finite laws.
It also uses $T_h\le\mathcal K$, so the returned interval is
$[\max\{T_h,3Q/5\},Q]$ and collapses to $\{\rho\}$ when $h\ge t$.

**These are rate-functional values, not achieved RMS errors.** The statistical
comparison between the rate and minimax risk is a paper proof with loose
constants. This calculator does not implement the rare-event estimator or
certify its execution budget. It does not infer a gap law from data or provide
an unknown-law confidence interval. Numerical values, including the comparison
endpoints, use floating-point arithmetic and are not interval certified.

To invert $Q$, replace `--budget` with `--target-rate`:

```sh
python -m threshold_toolkit rare-event --gaps 0.01,0.1,0.4 --weights 1,2,7 --rarity 0.05 --target-rate 0.01
```

For this example, $Q(B)$ reaches 0.01 at approximately
$B=1{,}130{,}446.692$. This is the threshold of the displayed functional;
it is not a recommendation that an implemented estimator will achieve
one percentage point of RMS error at that budget. Add `--json` for a
structured report, or use the Python API:

```python
from threshold_toolkit import FiniteGapLaw, RareEventProfile

law = FiniteGapLaw(gaps=[0.01, 0.1, 0.4], weights=[1, 2, 7])
profile = RareEventProfile(law, rho=0.05)
result = profile.evaluate(100_000)
print(result.value, result.selection_lower, result.selection_upper)
print(profile.tail_weights, profile.core_weights)

inverse = profile.budget_for_rate(0.01)
print(inverse.budget, inverse.status)
```

`FiniteGapLaw` normalizes relative weights, removes zero-mass entries and
merges duplicate gaps. Gaps must lie in $(0,1/2]$; weights must be finite and
nonnegative, with positive total mass. Positive weights that would disappear
during normalization are rejected. Omitting `weights` gives equal masses.
The entropy sums inverse-square costs **by dyadic band**, using the actual
gaps; it does not treat every atom as a separate scale.

The preprocessing takes $O(n\log n)$ operations, followed by $O(\log n)$
queries for either evaluation or inversion. Inversion uses the piecewise
linear expression in $h=B^{-1/2}$, without subset search or simulation.
Logarithmic costs keep the computation usable when an inverse-square cost
overflows an ordinary float. A target at least $\rho$ returns budget infimum
zero with status `saturated`. A required budget beyond the floating-point
range returns infinity with status `overflow` and a finite `log_budget`;
that is a representation limit, not an impossibility result. Finite returned
budgets approximate the threshold and can differ by roundoff.

The new API and its direct command need only the standard library:

```sh
python -m threshold_toolkit.rare_event_cli --gaps 0.01,0.1,0.4 --weights 1,2,7 --rarity 0.05 --budget 100000
python toolkit/examples/rare_events.py
```

## Assumptions and limits

- Items are drawn independently at random, and repeated tries of one item are
  independent. Drifting success rates or related items are not covered.
- The line is fixed at 50/50: "succeeds more often than not". Other thresholds are
  not supported.
- The simple plan's figures are only as good as your guess of how close items
  are to 50/50. If you build the guess from a small trial run, items can look
  more clear-cut than they are. Guessed rates of exactly 0.5 are rejected:
  the cited theorems assume no mass at that rate. Do not change a genuine tie
  just to pass validation; such populations need a model that includes ties.
- The proven method uses at most the budget you give it on average, and often
  noticeably less, because it rounds the budget down to four times a power of
  two. A single run can use several times the average.
- The execution API requires a finite budget of at least four flips. The
  standalone `two_success_average` requires iid calls, independent of its
  random generator, with finite values and strictly positive costs bounded by
  a finite positive cap. Zero-cost calls are rejected to prevent a nonterminating
  pilot, as are calls whose cost divided by the cap underflows to zero.
- What is machine-checked is the mathematical guarantee of the proven method, in
  [`BlindUpper/Full.lean`](../lean/ThresholdHC/BlindUpper/Full.lean), and the
  floor, in [`Tier6/Full.lean`](../lean/ThresholdHC/Tier6/Full.lean). This Python
  code is not itself verified. Its tests check it against a separate
  implementation of the paper's definitions, exact enumeration and the
  calibration identities.

## Research module: the rare-event selection functional

`threshold_toolkit.rare_event_functional` is a separate research computation,
not part of the calculators or the estimators. For a known finite gap law, the
calculator in section 3 evaluates $Q$ in floating point and brackets the
selection functional $\mathcal K$ by the $5/3$ comparison. This module instead
encloses $\mathcal K$ itself between exact rational bounds, by bandwise-suffix
enumeration whose cost grows exponentially with the number of occupied bands.
It also gives the cheaper bound $\frac58Q\le\mathcal K\le Q$. It uses only
the standard library and rejects floats as inputs. It is not imported by the
package itself, and its `FiniteGapLaw` is a different class from the
package-level one in section 3, so import it from
`threshold_toolkit.rare_event_functional`. Its bounds rest on paper proofs that
are not Lean-checked. See the
[certified-selection package](../research/2026-10-30-certified-selection/README.md)
for the mathematics and status; its
[note](../research/2026-10-30-certified-selection/NOTE.md#example-use) has a
usage example.

## Tests

```sh
python -m unittest discover -s toolkit/tests -v
```

Code is Apache-2.0 and this guide is CC BY 4.0, like the rest of the repository.
