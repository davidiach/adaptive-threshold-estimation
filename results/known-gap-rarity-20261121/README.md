# The known-gap estimator that needs no rarity: library audit

The adaptation note of the minimax audit
([`research/2026-10-27-minimax-audit/adaptation.tex`](../../research/2026-10-27-minimax-audit/adaptation.tex),
claim `A7` of its claims table) shows that at a known fixed gap the rarity
need not be known. One estimator per budget, built without $\rho$, buys $m$
flips from each of $n=\lfloor B/m\rfloor$ fresh coins, where $m$ is the least
odd integer at least $\log(2B)/(2d^2)$. It takes the share $\bar Z$ of coins
whose majority vote is heads, debiases it by the exact binomial tail
$f=P(\mathrm{Bin}(m,1/2-d)>m/2)$ as $(\bar Z-f)/(1-2f)$, and clips to
$[0,1]$. The note proves its mean squared error is at most
$8m\theta/B+4m/B^2$, and gives a conservative interval. The research package
recorded this as a paper proof. Lean now checks it, in
[`lean/ThresholdHC/KnownGapRarity`](../../lean/ThresholdHC/KnownGapRarity/Full.lean).
The research package is unchanged. The audit runs below were made at commit
[`8b59fd8`](https://github.com/davidiach/adaptive-threshold-estimation/commit/8b59fd8).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/KnownGapRarity/Specification.lean)
defines the flip count, the miss rate $f$ (the fixed-plan group's exact
binomial tail), the coin count, the debiased raw estimator, the clipped
estimator `knownGapEstimator d B`, and the radius
$r=\sqrt{\log(2/\delta)/(2n)}/(1-2f)$, which is $1$ for small budgets. The gap
law is the point mass $\delta_d$; $\theta=q(d)$ ranges over $[0,1]$ as the
sign law $q$ varies.

| Target | Statement |
|---|---|
| `flip_count` | For every gap $d$ and $B\ge1$, the flip count is odd, at least $\log(2B)/(2d^2)$, and at most every odd integer that is at least $\log(2B)/(2d^2)$. |
| `known_gap_rarity_free` | For $d<1/2$ and $B\ge1$, the estimator has a deterministic cap of $\lfloor B\rfloor$ flips and expected work at most $B$ under every sign law; for $B<2m$ it outputs zero, with squared error exactly $\theta^2$; and its mean squared error is at most $8m\theta/B+4m/B^2$ for every sign law. |
| `known_gap_confidence` | For $d<1/2$, $B\ge1$ and $0<\delta<1$, the interval $[\hat\theta_{\rm raw}-r,\hat\theta_{\rm raw}+r]\cap[0,1]$ misses $\theta$ with probability at most $\delta$ under every sign law; the same as `UniformConfidence` for the raw estimator, and for the interval centred at the clipped output. |

The bound for $B<2m$ follows from the zero output, a mild strengthening of
the source, which states the bound for $B\ge2m$. The clipped-centre interval
goes beyond the source. Not stated: the unbiasedness of the raw estimate as a
separate claim (it is used inside the risk proof), the order-of-magnitude
discussion, the endpoint remark at $d=1/2$, the computability of $f$, and the
shared-regression example of the same audit, which was split off and not
taken up. The hypothesis $d<1/2$ is kept to match the source; the proofs do
not use it.

## How the proofs go

- [`Cap.lean`](../../lean/ThresholdHC/KnownGapRarity/Cap.lean): every call
  has the same cost, so the plan's policy is the hard-budget `stopAt` at
  $n(2k+1)$ flips, and the public `stopAt_pathwise_cap` gives the cap.
- [`Miss.lean`](../../lean/ThresholdHC/KnownGapRarity/Miss.lean): Hoeffding
  gives $f\le e^{-2md^2}\le1/(2B)$, and $f\le1/4$ once $2m\le B$.
- [`Risk.lean`](../../lean/ThresholdHC/KnownGapRarity/Risk.lean): the vote
  mean is $f+(1-2f)\theta$ and its variance at most its mean, so the
  mean squared error is at most $4(\theta+f)/n\le8m\theta/B+4m/B^2$; clipping
  can only help, and the zero branch is direct.
- [`Confidence.lean`](../../lean/ThresholdHC/KnownGapRarity/Confidence.lean):
  the output event moves to the infinite coin table, where two-sided
  Hoeffding at $t=\sqrt{\log(2/\delta)/(2n)}$ gives the coverage.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_known_gap_rarity.py --replay --jobs 2` | 6 exact statements (the 3 targets and 3 components) and 69 transitive axiom reports over the 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [known-gap-rarity-audit.log](known-gap-rarity-audit.log) |
| `python -m unittest discover -s tools -p 'test_known_gap_rarity.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 20,355 constants (16,446 theorems) in 1,696 modules, same axioms. 155 exported instances; 6 registered orphans, unchanged. 3,763 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,697 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 11
entries to `tools/definition_lock.json`: the three statements and the eight
definitions above. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which split
off the shared-regression example as of very low value, kept the
statements, and asked for the interval also to be centred at the clipped
output. A third agent wrote the proofs. Before the specification was pinned,
a fourth agent that had not written them:
- rebuilt the modules, replayed them through the kernel checker and printed the axioms;
- restated the targets with their types written out;
- checked at $d=1/4$, $B=128$ that the nontrivial branch $2m\le B$ is reached, that the radius at $\delta=1/2$ is below one, and that the error bound at $\theta=0$ is below the trivial bound.

It found no defect in the Lean. Two of its minor points were acted on before
the pin: the target's docstring now names the bound on expected work and the
cap level, and the source's sentence that the zero estimator has error
$\theta$ for $B<2m$ is now a conjunct of the target, with the unbiasedness of
the raw estimate listed as not stated. The third concerned the location of
the implementer's report. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
