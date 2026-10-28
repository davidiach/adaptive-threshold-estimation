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

## Read this first: what building it showed

The paper proves a method that needs no tuning. It never needs to know how close
your items are to 50/50, and its guarantee is machine-checked. When we ran it at
everyday budgets, though, it was **much less accurate than a simple plan**: try
each item a fixed number of times and take a majority vote per item.

For the ten-item guess used in the examples below:

| | Simple plan | Proven no-tuning method |
|---|---:|---:|
| Typical error at 16,384 flips | 5.9 points | 28 points (simulated) |
| Flips for a 3-point typical error | 258,153 | about 4.2 million (simulated) |

In theory the proven method's error shrinks at the best possible rate as budgets
grow. In every case we tried, though, the simple plan needed far fewer flips. So
the calculator gives you the simple plan's numbers and shows the proven method
beside them. The proven method's real advantage is
robustness: the simple plan is only as good as your guess of how close the items
are to 50/50, while the proven method needs no guess at all.

## Install

Python 3.10 or newer with NumPy. Either install it:

```sh
pip install ./toolkit
```

or run from the `toolkit/` folder without installing. The estimators themselves
need only the standard library; NumPy is used by the calculator.

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
    flips used: 15,538 on average; 90% of runs used at most 31,091, 99% at most 46,572

  On your guess, the simple plan's typical error is 4.7x smaller.

  Proven limits, for every way items this close to 50/50 could fall:
    difficulty score: 0.0951
    no method can promise a typical error below 0.00149 (difficulty / 64)
    the no-tuning method is proven to stay within 48.7 (difficulty x 512), too loose to be useful here

  Returns on more flips: 4x the budget would cut the difficulty score to 50% of today's.
    (50% is the best case, when every item is far from 50/50.)
```

How to read it:

- **Hard to call** counts items so near 50/50 that even the whole budget spent
  on one of them would leave about a 2% or larger chance of placing it on the
  wrong side.
- **Typical error** is the root-mean-square error: roughly how far off the
  estimate usually is. 0.059 means about 6 percentage points.
- **"at most … however these items fall"** is exact arithmetic, not simulation. It
  holds for any items this close to 50/50, whichever side each one is on. You
  could have the sides wrong in your guess and it still holds; only the
  closeness has to be right.
- **The proven method's numbers are simulations** of the actual algorithm on your
  guess. Its budget is an average, so single runs vary; the 90% and 99% figures
  show by how much.
- **Proven limits** come from the paper's machine-checked theorems. The floor
  says no method of any kind can do better in the worst case. Both limits are
  very loose (a factor of about 30,000 apart), which is why the simulation is
  there.
- **Returns on more flips**: when many items sit near 50/50, extra flips buy
  less.

With `--target-error 0.03` instead of `--budget`, the calculator finds the
cheapest simple plan whose worst case meets the target. It also simulates the
proven method at doubling budgets until it meets the target too, giving up at 64
times the simple plan's flips.

Use `--runs` to change the number of simulated runs (default 200) and `--seed` to
change the simulation's seed.

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

## Assumptions and limits

- Items are drawn independently at random, and repeated tries of one item are
  independent. Drifting success rates or related items are not covered.
- The line is fixed at 50/50: "succeeds more often than not". Other thresholds are
  not supported.
- The simple plan's figures are only as good as your guess of how close items
  are to 50/50. If you build the guess from a small trial run, items can look
  more clear-cut than they are, so lean towards guessing them closer. A guessed
  rate of exactly 0.5 means a true coin toss that no amount of trying can place
  on either side; if an item is only roughly even, guess 0.49 or 0.51.
- The proven method uses at most the budget you give it on average, and often
  noticeably less, because it rounds the budget down to four times a power of
  two. A single run can use several times the average.
- What is machine-checked is the mathematical guarantee of the proven method, in
  [`BlindUpper/Full.lean`](../lean/ThresholdHC/BlindUpper/Full.lean), and the
  floor, in [`Tier6/Full.lean`](../lean/ThresholdHC/Tier6/Full.lean). This Python
  code is not itself verified. Its tests check it against a separate
  implementation of the paper's definitions, exact enumeration and the
  calibration identities.

## Tests

```sh
python -m unittest discover -s toolkit/tests -v
```

Code is Apache-2.0 and this guide is CC BY 4.0, like the rest of the repository.
