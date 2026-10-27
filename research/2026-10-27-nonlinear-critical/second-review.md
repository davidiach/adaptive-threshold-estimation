# Scoped second analytic review

Date: 2026-10-27. Reviewer role: formal-foundations / alternate analysis.
**Finding:** no blocking defect found in the reviewed finite-convex and
population-wrapper arguments at the source identities below. This is a
paper review by another agent, not a Lean check, external specialist
review, or novelty certification.

## Independence and exact reviewed sources

I authored `base_cost.md` and its TeX adaptation. I also contributed a
derivation of the finite-prefix Hellinger product inequality and the
separate Poisson-partition exploration. I therefore do **not** describe
this as a fully independent review of the complete result. The parent
wrote `unrestricted.tex`, the construction role wrote
`affine_comparison.tex`, and the adversarial role reviews all components
independently of their authorship. Model diversity is not guaranteed.

The distinct components I read and checked were:

| Source | SHA256 at this review |
|---|---|
| `unrestricted.tex` | `9ecff9c7534ba883bd6d1fdfc6340c70956486ac666f219ed991dba879d188d6` |
| `affine_comparison.tex` | `c243a6ad355aeabb2fea3df195166faf066b95b4e5778e3bc02512d61a80f7c2` |
| `upper_bound.tex` | `e4d8fd72f87fe0bf590b1cbbf8a61d9736f1402ba5e6a364df834cc810737fbc` |

The dependency I authored, rather than independently reviewed, is
`base_cost.tex`, hash
`6c02a467ac9a8b989ccb3e3618a9bb567e332ed1d3830d70fca27c01e5e3265a`.
Its source Markdown received a separate independent adversarial review.
No compiler or proof assistant acceptance is inferred from this table.

## Convex-experiment and simultaneous-pair check

I checked the full finite experiment fragment, including the following
points rather than treating convexity as sufficient by itself:

- The stopped one-coin statistic `(T, number of heads)` is sufficient even
  when the independent seed is continuous and the stopping rule depends
  on the ordered bits. Conditional on that statistic, the common
  integrated Bernoulli-word likelihood cancels. Zero seed-mass cells are
  removed; all remaining cells have positive probabilities for the fixed
  interior-gap law.
- The finite image retains `theta` as a coordinate. Thus nonidentifiability
  from observed cell probabilities is permitted. The compact weak-star
  image is convex, and its affinity is continuous and jointly concave.
- The saddle proof uses an additive score space with finite exponential
  moments. Its affinity constraint, diagonal bound on the exponential
  scale, and integration of a single estimator's tail justify RMS
  comparison. This does not confuse confidence risk with RMS risk.
- The index-selected single-coin reduction preserves the mean and has
  base cost exactly `E_0 T_A`. The common-mass inequality controls its
  uniform variance by `(7/3)n r^2`. It applies to bounded finite-cell
  scores without imposing moment assumptions on an arbitrary nonlinear
  estimator.
- In the hard-pair extraction, both cases of the integer sample-size
  choice are covered, including zero base cost. The pair separation is
  fixed before policy selection in the final lemma.
- Revealing a mixture index makes the Hellinger distance exactly affine
  in the policy mixture. Finite-simplex minimax and compactness then give
  the finite intersection argument. An unrevealed-mixture identity or a
  topology on the entire policy space is not assumed.

## Population passage, model, and stopping

The full experiment explicitly fixes the policy before the unknown `q`
and supplies only an independent seed and observed histories. The stated
latent-uniform construction realizes the exact quadratic law and every
measurable sign allocation. Numbering by first charged observation is
justified by independence of unused iid coin states; it retains every
later revisit and gives at most `K` observed slots at a prefix of `K`
flips. There is no global finite-coin assumption.

At a fixed original seed, each feasible finite leaf has the product of
its per-coin ordered-word likelihoods. Feasibility is determined by the
seed and the observed bits. Interleaving changes the words and tree, not
this product rule. The midpoint probability of a word is exactly the
arithmetic mean of its two endpoint probabilities, because the latent
sign mixture is affine in `q`.

The product inequality in the wrapper compares a normalized midpoint
leaf law with the endpoint geometric mean. Summing it yields the sum of
normalized one-slot hybrid Hellinger distances in the convention
`h=1-Aff`, with no missing factor of two. Hybrid simulations use fixed
reference tapes only inside the comparison policy. Their full independent
simulation seed may reveal more than the hybrid transcript; data
processing goes in the needed direction. Knowing the fixed reference
pair does not let this policy depend on which endpoint supplies its
genuine coin. The universal-pair quantifier covers every such fixed
policy.

Because the midpoint sign allocation is at most `1/2`, its latent law
dominates one half of the all-negative law, and hence the null expected
work is at most twice the midpoint expected work for that same policy.
Summing the midpoint slot costs recovers exactly the actual prefix cost.
This is the point at which the strengthened base-cost input is essential;
a bound using separate worst-case work would not suffice.

One common pair works for every finite cap. The selected constant `gamma`
makes each prefix satisfy `h<=1/8`, hence total variation at most `1/2`.
Finite expected work gives separate almost-sure termination at both
endpoints. Approximating a terminal event by its stopped-prefix events
then passes this TV bound to the terminal experiment. No unbounded
optional-stopping identity, KL chain rule, or differentiability assumption
is used. Threshold testing gives RMS at least one quarter of the target
separation, including the saturated branch.

## Variational modulus and upper checkpoint

I recomputed the three intervals `(0,h]`, `(h,t]`, and `(t,a]` in the
unsaturated variational formula. Their sum is exactly
`[2ht(1+log(a/t))-h^2]/a^2`. With
`rho=u exp(1-u)` and `L=u-log u`, the bounds `L<=u<=2L` give the stated
comparison to `min(rho,sqrt(rho L/B))` with the fixed `a=1/4`.
For `rho_n=exp(-exp(n))` and `B_n=rho_n^(-2)`, both claimed risks are
eventually unsaturated, and their ratio grows as at least a positive
constant times `sqrt(1+log L)`. This comparison does not identify the
compactness-selected hard pair with the radial variational optimizer.

I also reread the inherited upper restatement. The asymmetric crossing
bounds and forced-majority errors apply under the actual global rarity
constraint. The drift-selected reference lies in `[d/4,d/2]`; the work
cap and the small-gap case fit the same minimum bound. The rearrangement
bound for positive work uses a total positive mass constraint. The level
differences use the same genuine coin with independent unused blocks,
and their absolute summability is established before telescoping signed
means. The displayed second moment `165rho/56` and work
`1350 a^(-2)LH` follow from the stated geometric sums. Independent Poisson
replication and the zero-work constant branch then give the full uniform
upper rate. This is reused prior work, not a new construction.

## Exact finite-prefix diagnostic

The new `check_prefix.py` uses exact `Fraction` probabilities and work,
with certified 160-bit dyadic enclosures for nonrational square roots.
The squared enclosure endpoints are checked exactly; rational square
roots are recognized exactly. It enumerates fixed observable finite
trees at caps 2, 4, and 6 for two- and three-atom laws, including
interleaving, observation-dependent creation, early stopping, and a
revealed mixture containing a zero-observation branch. Zero-cap cases
are also checked. These atomic examples test the finite-prefix algebra,
not the critical continuous-law entropy theorem.

The command, from the repository root, was:

```powershell
python research/2026-10-27-nonlinear-critical/check_prefix.py
```

The final run exited **0**: 20 population cases and two stopped-statistic
cases passed. It checked every endpoint, midpoint, and one-slot hybrid
normalization; affine word probabilities; the Hellinger decomposition;
null-cost domination by twice midpoint cost; exact work summation; and
the population-independent conditional seed/word law given `(T,heads)`.
The largest enumerated experiment had 185 revealed-seed leaves. No
Monte Carlo, optimization, random seed, or tolerance-based assertion was
used. The output contains exact fractions and enclosures.

The first implementation run exited 1 on a zero-cap equality because a
non-dyadic rational square root was enclosed rather than recognized
exactly. Adding exact perfect-square recognition fixed that diagnostic
issue; no proof source changed. Both the failed check and its repair are
disclosed here rather than presented as a mathematical counterexample.

| Artifact | SHA256 |
|---|---|
| `check_prefix.py` | `d6f4aa173b7922991fb0d83a1e9bed6231e60ec1236ad1f0389e3920aac3fef2` |
| `check_prefix_results.json` | `a4d4d725e0511297ab0f29cfdd41450ff59328b227b8ce4b3dfa0e139c1b4b02` |

For a replay without replacing this record, pass an unused path with
`--output`. The source hash and deterministic result data can be compared
exactly. These finite checks cannot certify the simultaneous hard pair,
the infinite transcript limit, or the full mathematical theorem. Those
remain claims established, if accepted, by the paper proof and its scoped
reviews.

## Final source pass

I reread the complete wrapper after the parent updated the title, review
status, attribution, and bibliography. Its mathematical statements and
proof steps match the version reviewed above. The new explicit
Juditsky--Nemirovski and Polyanskiy--Wu credit correctly distinguishes the
existing convex-estimation principles from the proposed critical-law
application. No new blocking finding was identified.

The final four-file source identity for this scoped review is:

| Source | Final SHA256 | This reviewer's role |
|---|---|---|
| `unrestricted.tex` | `b00b608ca1012148934e5717d2b10ee1d1379fa312a9f5bf06a0ac1e0e6fb853` | Wrapper, stopping limit, modulus and upper-replication review; contributed a direct-sum derivation |
| `base_cost.tex` | `6c02a467ac9a8b989ccb3e3618a9bb567e332ed1d3830d70fca27c01e5e3265a` | Author; not independently reviewed by this agent |
| `affine_comparison.tex` | `c243a6ad355aeabb2fea3df195166faf066b95b4e5778e3bc02512d61a80f7c2` | Separate analytic review of construction agent's fragment |
| `upper_bound.tex` | `e4d8fd72f87fe0bf590b1cbbf8a61d9736f1402ba5e6a364df834cc810737fbc` | Rechecked inherited construction and constants |

The parent reports successful built-in TeX compilation; I did not run a
second compiler and make no independent compilation or Lean claim. The
exact finite-prefix diagnostic execution reported above is this agent's
own execution. The full independent adversarial review, with its own
source identities, remains the appropriate record for independence of
the complete mathematical chain.
