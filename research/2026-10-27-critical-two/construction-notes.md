# Critical-margin construction attempts

This record concerns the ordinary iid fresh-coin model with hidden D and S,
known exact power law F(d)=(d/a)^2, known rho, and only the global constraint
integral q dmu <= rho. It does not replace earlier notes.

## Starting point rechecked

The earlier alpha>2 result is preserved. The separately owned current
`research/2026-10-27-minimax-audit/theorem/critical.tex` already proves the
critical upper bound with unbiased single-coin second moment at most
165 rho/56 and work at most 1350 a^-2 L(1+log L), where L=1+log(1/rho).
This was read before choosing the new target; reproducing that bound is not
counted as progress.

## Attempt 1: remove dictionary weights by average false-positive accounting

Proposed positive likelihood boundaries of order
epsilon^-1 max(1,r^2/t^2). A sharper wrong-sign crossing estimate integrated
against the power-two law could distribute false-positive error across scales
without paying uniform dictionary entropy. However this does not control
false negatives for positive coins. Positives can concentrate at a gap having
many larger reference scales, each presenting an early nearly-fair wrong-sign
crossing opportunity. A constant negative boundary across scales cannot simply
be treated as a uniformly accurate sign classifier.

Status: parked; no upper theorem claimed. The missing step is a signed or biased
response that avoids demanding uniformly accurate per-coin sign decisions.

## Attempt 2: ballot survival and adaptive amplification

For a fixed time n, the standard ballot-weight output
(n/S_n) 1{S_1,...,S_n>0} has mean P(S_n>0). Its positive second moment has an
inverse-gap loss. Amplifying the coin at a scale t would control that moment,
but a fixed block costs t^-2 on easy negative coins; an adaptive sign amplifier
must address the multiscale sign-testing obstruction. No observable unbiased
amplifier with the required average work was obtained.

Status: parked; no computational failure is treated as impossibility.

## Revised structural target

The entropy obstruction can be made rigorous for *every* unbiased single-coin
estimator, not merely a chosen classifier family. The parent suggested
conditioning on the first-observation event to remove artificial thinning and
prove a product lower bound without prescribing how variance and work are
balanced. The resulting proof is in `construction.tex`.

For the single fixed law a=1/4, it proposes the sharp characterization

    inf_A (sup_q Var(Y_A)) (sup_q E T_A)
        = Theta(rho L (1+log L)),

over single-coin estimators unbiased for every q in the global-rarity class,
with finite separate uniform bounds. Policies may depend on rho, use arbitrary
independent seeds, stop before sampling, and have unbounded stopping. The lower
proof uses an explicit finite-grid Bernoulli sign-testing entropy lemma and
does not rely on numerical experiments. The upper side reuses the existing
critical theorem cited above.

This is a restriction on a broad estimator class, not a refutation of the
all-algorithm minimax conjecture. Biased estimators and cross-coin algorithms
are not reduced to this class. The principal full upper/counterexample task
remains open unless a further valid reduction or new construction is supplied.

## Evidence status

Paper proof checked in two separate agent reviews. No Lean target
or accepted formal theorem is claimed. Model diversity among agents is not
guaranteed. The entropy ingredient has substantial prior-art overlap with
Chen--Li--Qiao; no priority claim is made for that ingredient or for the final
specialized characterization before a broader source comparison.

## Reviewed strengthening: small uniform bias does not remove the loss

The complete canonical theorem and proof are now in `construction.tex`,
Theorem `thm:bias` and its proof section. The earlier derivation in this ledger
was promoted there after two separate agent reviews; this ledger retains only
the attempt history and the scope distinction.

For the same fixed law a=1/4, the sharp single-coin product order
Theta(rho L (1+log L)) remains true when exact unbiasedness is replaced by
uniform absolute bias at most rho/64. This includes arbitrary per-coin
stopping, independent seeds, pre-observation thinning, and all moment/work
allocations. The new ingredient is a response bad-set argument obtained from
q=1_E alternatives of mass rho; it requires no pointwise response identity.

The proof preserves the main unbiased theorem separately. The upper checkpoint
is restated in a TeX appendix and pinned to source commit
`a8a8dc49115aabdd1fba8d53d3390eb0a5eee864` and source SHA-256
`0e8b9eaf762b3b09fa0d92ce1a036c2ceea8c12d00a5eea8286b852f36a81536`.
That upper theorem predates this attempt and is not counted as its discovery.

## Reviewed strengthening: heterogeneous noninteractive additive estimators

The parent supplied a further reduction, independently checked by both
reviewers before integration. The canonical statement and proof are now
Theorem `thm:additive` and its proof section in `construction.tex`.

The class permits a shared independent seed, heterogeneous own-coin policies,
random signed weights, and an almost surely finite preselected count N with
finite mean, including an unbounded Poisson count. Conditional on the shared
seed, the genuine coins and local randomness are independent. The final
output is an offset plus the sum of component outputs. Explicit separate
square-integrability conditions and finite expected work are imposed.

The proof compares each component to the known all-negative law: their output
laws share latent mass 1-theta, so a mixture-variance inequality controls the
component mean shift. A seed law reweighted by N, followed by a uniformly
selected component, converts the entire additive procedure into one low-bias
single-coin estimator with variance at most (7/3) E[N] times the original
uniform variance and expected work divided by E[N]. The same entropy product
lower bound therefore applies.

For this precise class the minimax RMS is now characterized as

    Theta(min(rho, sqrt(rho L (1+log L)/B))).

No unbiasedness assumption is needed for this RMS statement: error below
rho/64 implies the required bias bound, and larger errors supply saturation.
The existing Poisson upper construction and constant estimator attain the
matching order and meet the square-sum assumptions.

This is stronger than an obstruction to one classifier family or to identical
averaging. It still does not cover nonlinear final aggregation such as
clipping, observation-dependent design/counts, or genuine cross-coin feedback.
The unrestricted critical minimax problem remains open.
