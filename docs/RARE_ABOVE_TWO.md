# Observable rare events above the inverse-square boundary

The [full theorem package](../lean/ThresholdHC/RareAboveTwo/Full.lean) proves the
alpha > 2 rare-event RMS rate in the existing observable adaptive experiment.
For the exact power law on (0,a],

$$\frac{1}{256}\min\!\left\{\rho,\frac{\sqrt\rho}{a\sqrt B}\right\}
\le R_{\mu,\rho}(B)
\le C_\alpha\min\!\left\{\rho,\frac{\sqrt\rho}{a\sqrt B}\right\}.$$

The parameter range is alpha > 2, 0 < a <= 1/2, 0 < rho <= 1/4, and B >= 1.
The upper coefficient is finite for every fixed alpha > 2; no uniform bound
as alpha approaches 2 is claimed.

## Statements and observation model

The seven full targets were compiled and frozen at `a2b65da` before supporting
proofs. Their [specification](../lean/ThresholdHC/RareAboveTwo/Specification.lean)
and all 33 imported project dependencies are protected by the
[original hash lock](../tools/rare_above_two_specification_freeze.json).

| Target | Formal result |
|---|---|
| `power_law_exists` | A probability law on actual gaps with the exact power CDF exists for every admissible exponent and scale. |
| `rare_single_coin` | One observable family depending only on a and rho is unbiased, has second moment at most 28 rho, and actual expected work at most W(alpha)/a^2. It only queries coin 0. |
| `rare_supported_lower` | The 1/256 lower bound holds for every gap law supported below a and every admissible adaptive estimator. No power-law assumption is needed here. |
| `above_two_upper` | For each alpha, one family depending on a, rho and B works uniformly over the whole power-margin class, with risk at most min(rho/2, C(alpha) sqrt(rho)/(a sqrt(B))). |
| `above_two_minimax` | Matching minimax rates for the exact power law. |
| `above_two_psi` | The actual variational Psi functional is comparable to min(rho, h sqrt(rho)/a) for the exact power law. |
| `rare_nonvacuity` | The budget class contains a zero-work estimator returning rho/2, which also bounds the minimax risk. |

All statistical statements use `Tier6.experimentLaw`, `expectedWork` and
`rootMeanRisk`. The algorithm observes its seed and flips. Magnitudes and signs
remain hidden; labels are unrestricted natural numbers, and revisiting and
interleaving are allowed. Cost counts actual flips. Squared risk is extended
valued, so infinite-error algorithms remain in the model.

Rarity means the global restriction integral q dmu <= rho. It does not require
q(d) <= rho at every magnitude. The upper rule is chosen before mu and q; it
uses alpha only through the budget-calibration constant. The single-coin family
is chosen before alpha as well.

## Proof map

The upper construction uses asymmetric, stage-dependent dyadic boundaries.
The wrong-positive error is scaled by rho. Power-tail and weighted-moment
estimates turn the global rarity restriction into a uniform work bound.
A geometric random-level telescope produces an integrable unbiased output,
with second moment at most 28 rho. `Controller`, `Execution` and `Realization`
identify its output and work in the actual observable experiment.

Independent fixed-count repetitions reduce variance. `FixedExecution` and
`FixedIdentities` prove their execution semantics, and `Budget` chooses either
this average or the zero-work rho/2 estimator for every budget. This formal
construction proves the same rate with conservative constants. It does not
certify the paper's 153/56 single-coin constant or its compound-Poisson
implementation.

The lower proof establishes a finite-path information bound charged separately
to each queried label. Bernoulli KL controls gaps below 1/4; a variation bound
covers the remaining range, including deterministic endpoint coins. A quadratic
rare-mixture inequality, averaging over hidden signs and magnitudes, and the
existing midpoint hybrid decomposition give an information charge proportional
to a^2 times actual work. The proof then handles unrestricted labels and seeds,
finite expected-work termination, terminal decisions and two-point risk.
The constant priors rho/2 and rho/2 + delta lie inside the full rarity class.
No Lee–Valiant statistical theorem is assumed as an axiom.

The formal Psi comparison is separate from the statistical construction.
It does not establish a general-law matching-Psi theorem, which the critical
quadratic counterexample already rules out.

## Reproduction and remaining scope

```sh
python tools/verify_rare_above_two.py --sequential
python -m unittest discover -s tools -p 'test_rare_above_two.py' -v
```

The audit rebuilds all 54 registered modules, checks the seven exact frozen
types and reports every named declaration's transitive axioms. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. The guards reject changed
specifications or imported models, omitted targets or modules, wrong dependency
order, incomplete reports and nonstandard axioms. Fresh reports go under
`.runtime/rare-above-two/`; CI runs the same audit.

The paper-only rare-event regimes below two, sharp rare-event confidence rates
at and above two, and a corrected arbitrary-law characterization remain outside
this package. This formalization does not establish novelty or external
specialist review. Historical manuscripts and research bundles retain their
original proof constructions and checkpoint labels; this guide records the
new formal coverage.
