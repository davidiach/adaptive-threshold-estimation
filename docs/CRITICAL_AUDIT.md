# Critical quadratic theorem: follow-up audit

## Scope and source identity

This audit starts from the four-file proof bundle at published commit
`b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`. Its identities are recorded in
[the existing checkpoint](../research/2026-10-27-nonlinear-critical/CHECKPOINT.md).
The audit is an additional AI source review, not human specialist review or a
new certificate for the full theorem. Existing positive reviews are evidence
to examine, not premises in the proof.

The proposed result concerns the fixed law `mu(dd)=32d dd` on `(0,1/4]`,
every measurable `0<=q<=1` with `integral q dmu<=rho`, and arbitrary observable
fresh-coin algorithms with a uniform expected-flip budget. Set
`L=1+log(1/rho)` and `H=1+log L`. The claimed RMS order is
`min(rho,sqrt(rho L H/B))`. The lower argument uses the subclass `q<=1/2`;
the upper claim must still cover the full class.

## Initial dependency audit

The following records checks of actual arguments, with their remaining proof
obligations. No blocking mathematical error has been established in this first
pass. That is weaker evidence than an independently reconstructed or formal
proof.

| Dependency | Check performed | Remaining verification |
|---|---|---|
| Finite-gap sign entropy, BC2 | Early decisions use deterministic-prefix KL, not optional stopping under the fair coin. The events share one terminal time, making the scale-window overlap argument applicable. The fair law need not terminate. | Formalize the probability comparison, overlap count, and analytic implication BC4 -> BC2. |
| Conditional moments and response | The populations `q=0` and `q=rho` give finite conditional second moments and work outside a common null set. The response bound comes from expectations before pointwise means are used. | Formalize conditional integration and variance decomposition. |
| First-observation normalization | The activation event is seed-only. Under its conditional seed law, `Z=pY+c` preserves means and changes null work to `W0/p`; the zero-activation case contradicts the bias requirement. | Construct the conditional procedure and verify its moment identities. |
| Good-gap selection | The proof uses populations `(1/2)1_E` with `mu(E)=2rho`, respecting the lower subclass's pointwise cap. The excluded mass is at most `70m`. | Formalize nonatomic subset selection and annulus averaging. |
| Sign-test restarts | Restarting on unused flips of the same coin preserves its latent gap and sign. Conditional iid suffixes justify independent outputs; it does not draw new magnitudes. | Prove the stopped-suffix realization and expected-work identity. |
| Finite observation reduction | At cap `m`, each seed/word cell has the integrated likelihood determined by `(T,heads)`. The multiplier cancels from conditional seed/word laws. | Formalize sufficiency, including arbitrary measurable seeds. |
| Convex RMS comparison | Finite categorical probabilities are affine and positive; log moments are concave in the population and convex in the score/scale. Tail integration is used to obtain RMS, rather than substituting a confidence bound. | Kernel treatment of the minimax interchange and tail integrals remains open. |
| One pair for all policies | The separated-pair set is compact convex in the weak-star topology. Squared Hellinger is continuous convex. A revealed finite policy mixture has exactly averaged Hellinger and null work. Finite-simplex minimax supplies the finite intersection property. | Formalize the compactness and minimax steps; a policy-dependent hard pair alone would not suffice. |
| Interacting population transfer | Leaf likelihoods factor by genuine coin even with interleaving. The midpoint hybrid simulations use independent auxiliary tapes. Since midpoint `q<=1/2`, its one-coin law dominates half the null law, giving the required cost direction. | Formalize the finite-prefix decomposition and simulation. Existing finite examples do not prove the general statement. |
| Unbounded stopping | The same pair applies at every cap. Uniform work gives termination separately under both endpoints; terminal events are approximated by stopped-prefix events. | Prove the limit without assuming termination transfers from one endpoint to the other. |
| Upper construction | Wrong-sign likelihoods are supermartingales; forced-majority error is bounded on the complete iid tape. Positive work is integrated under a global mass constraint, not a pointwise bound on `q`. The random telescope and Poisson replication use separately finite moments. | Full probability and algorithm realization remain paper arguments. |

## Specific constants and edge cases checked

* In BC5, `(1-rho)(31/32)^2 >= 2/3` on `0<rho<=1/4`; this also justifies
  replacing the raw second moment by at most `3V`/`2` in BC6.
* In BC7, the active procedure has `W0Z>=1`, `pM>=rho/6`, and
  `m<=4pM`. These inequalities retain null-population work throughout.
* In BC8, `4rho<=6m` makes `64m+4rho<=70m`. Every retained annulus has
  mass at least `140m`, so it cannot be swallowed by the excluded set.
* For `m/rho>=2/3`, the restart count satisfies
  `ceil(512(1+m/rho))<=1282m/rho`.
* The annulus comparison uses `d_j^2/mu(I_j)<=4a^2/3`; the averaging
  factor four gives the displayed `16a^2/3` work charge.
* Zero-work capped policies have population-independent transcripts. The
  hard-pair proof handles this case before any division by work.
* The statistical modulus is not identified with the variational optimizer's
  population profile. The claimed hard pair is existential.

## Primary-source checks

The follow-up consulted [Sion's original paper](https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf)
and [Chen--Li--Qiao](https://arxiv.org/html/1608.06031v2). Sion's convexity,
semicontinuity and compactness requirements must be discharged at each use.
The latter provides prior-art context for scale entropy, and its Remark D.4
explicitly extends the mechanism to interior Bernoulli laws. This agrees with
the earlier source audit. The present arbitrary separated gaps, error level,
and displayed constants still require the written adaptation; the Bernoulli
extension itself is not a new contribution. This is a targeted dependency check, not a search
establishing novelty or publication priority.

## Formalization boundary and first checkpoint

Two exact component targets and all nine public declarations now pass the local
Lean audit using only `propext`, `Classical.choice`, and `Quot.sound`:

* [Packing.lean](../lean/ThresholdHC/CriticalEntropy/Packing.lean) proves the
  probability-space event-packing inequality and the implication from BC4 to
  `c >= log(K)/512` for `log(K)>=32`. BC4 is an explicit hypothesis of the
  latter theorem. Constructing the sign-test events is still required.
* [CommonPoint.lean](../lean/ThresholdHC/CriticalEntropy/CommonPoint.lean) proves
  the abstract quantifier interchange: on a nonempty compact convex set, a
  family of continuous convex constraints admits one point satisfying all of
  them if every finite convex mixture has some feasible point. The proof uses
  a finite-simplex saddle point and compactness. Realizing the population-pair
  set, proving its weak-star compactness, and establishing the statistical
  mixture bound remain separate obligations.

[Specification.lean](../lean/ThresholdHC/CriticalEntropy/Specification.lean)
states these targets without importing their proofs; the audit checks exact
types. These specifications were introduced alongside the proofs, not frozen
beforehand. [Recorded evidence](../results/critical_components_001.json) contains
the source identities, commands, exit codes and transitive axioms. Reproduce it
with `python tools/verify_critical_components.py`; fresh output is written under
the ignored `.runtime/critical-components/` directory.

This checkpoint does not prove the finite-gap sign-testing theorem, the
base-cost theorem, or the full critical minimax law. The subsequent target is
the actual Bernoulli sign-testing theorem and its use in the base-cost argument.
The full completion criteria remain in [WORKPLAN.md](WORKPLAN.md).

## Constructed Bernoulli prefix information

The next checkpoint connects probability measures to the information step.
[BernoulliPrefix.lean](../lean/ThresholdHC/CriticalEntropy/BernoulliPrefix.lean)
proves that an arbitrary common independent seed and `n` iid Bernoulli flips
have KL exactly `n * klB(p,q)`. The proof constructs the finite likelihood
density, proves the product identity, identifies finite prefixes of the
infinite iid law, and applies data processing to any measurable statistic of
the seed and prefix. Its upper bound is derived from the flip probabilities;
no information inequality is an assumption of the statistical target.

[EventInformation.lean](../lean/ThresholdHC/CriticalEntropy/EventInformation.lean)
proves the resulting event transfer. In particular, if an event at a finite
prefix has probability at least `1/4` under parameter `p` and
`n*(p-1/2)^2 <= 4*c+1/4`, its probability under the fair coin is at least
`exp(-64*c-8)`, matching BC3. The seed space is arbitrary, and no fair-coin
termination hypothesis occurs.

These statements do not yet construct the events from a general stopping
rule. The remaining finite-gap steps are the early-decision bound, the
Markov window, and the overlap bound for geometrically separated gaps,
followed by their composition with the existing packing theorem. The null-cost
base theorem additionally needs the restart and good-gap selection arguments.
Four exact component targets and 25 declarations are checked by the expanded
audit; [the second record](../results/critical_components_002.json) preserves
their source identities and axiom reports. The original record remains a
record of the earlier, narrower checkpoint.
