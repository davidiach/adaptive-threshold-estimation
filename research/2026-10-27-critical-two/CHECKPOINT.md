# Critical quadratic margin: assessed research checkpoint

**The unrestricted Psi conjecture remains open.** This attempt obtained neither
a matching upper bound for every eligible algorithmic setting nor a lower bound
refuting it for arbitrary population procedures. It does obtain a sharp
characterization of a broad, explicitly restricted estimator class.

## Strongest new statement

Fix a=1/4 and mu with F(d)=(d/a)^2 on (0,a]. Put L=1+log(1/rho) and H=1+log L.
For every 0<rho<=1/4 and B>=1, the minimax RMS risk within the noninteractive
additive class specified in `construction.tex` is

    R_add(B) = Theta(min{rho, sqrt(rho L H / B)}),

with universal constants. The design may know mu,rho,B. It must work for every
measurable q with integral q dmu<=rho, while observing neither D nor S.

The class permits a common independent seed U, a seed-preselected count N that
is almost surely finite with E N<infinity, and heterogeneous single-coin
procedures. Conditional on U, each component uses its own genuine iid reservoir
coin and local randomization, and may stop at an unbounded time using its own
history. The final output is c(U)+sum_(i<=N) Y_i. The note states separate
square-integrability, square-sum and expected-work conditions. It permits
shared randomization and Poisson counts, but no observation-dependent count,
feedback between components, or nonlinear final postprocessing.

For the same fixed law, the preceding product theorem states

    inf_A [sup_q Var(Y_A)] [sup_q E T_A] = Theta(rho L H)

over all single-coin procedures with uniform absolute bias at most rho/64.
The unbiased subclass has the same order, and raw second moment can replace
variance. No variance/work allocation, finite stopping horizon, numerical
policy family, or attained optimum is assumed.

The exact candidate Psi is comparable to min{rho,sqrt(rho L/B)} at this fixed
a. Thus the new result rules out a uniform matching-Psi bound throughout the
specified additive class: in the nonsaturated joint limit it loses sqrt(H).
It does not rule out a successful nonlinear or interactive procedure.

## Proof and what is new in this workspace

The complete proof is `construction.tex`, with separate mathematical reviews
in `review.md` and `second-review.md`. Status: **paper proof with two agent
reviews**, not Lean-checked, not externally specialist-reviewed, and without a
priority claim. Reviewers did not author the proof they judged; the parent
supplied the normalization and additive-reduction ideas. Model diversity is
not guaranteed. The final source hash is recorded by those reviews and the
checkpoint lock/validation record.

The lower proof first forces a large conditional response on almost all useful
gap scales from the global bias guarantee. Conditioning on making a first
observation removes artificial thinning without assuming how work and variance
are balanced. Independent restarts on the same fixed coin then produce one
accurate sign test at many separated gaps. A finite-prefix entropy argument
forces integrated work of order K log K with K comparable to log(1/rho).
It never assumes termination of the auxiliary test at a fair coin.

For the population extension, the two output laws of each component under q
and under the known all-negative baseline share a submeasure of mass 1-theta.
The resulting mean-shift/variance inequality controls the cost of selecting
one component. Reweighting the independent seed by N/E N and selecting a
uniform component produces a valid single-coin estimator with the original
mean, at most (7/3)(E N) times the separate uniform population variance bound,
and work divided by
E N. This reduces the additive class to the small-bias product theorem.
An RMS/bias dichotomy supplies saturation without a bias premise on R_add.

The matching upper was **already present** in another owner's critical note,
now committed at `a8a8dc49115aabdd1fba8d53d3390eb0a5eee864`. Its estimator has
E Y²<=165rho/56 and E T<=1350 a^-2 L H. Our note restates the needed argument
with exact provenance, then uses established Poisson replication. Neither the
upper construction nor Poisson randomization is claimed as this turn's new
contribution. The new lower bound and its population reduction establish why
that upper order is sharp in the specified class.

## Competing attempts and numerical evidence

`construction-notes.md` records the failed average-error likelihood and ballot
survival approaches. `alternative.md` records the dictionary-allocation
certificate, failed SIGN simulations, and the attempted projection of a
general population estimator. The projection lacks an observable, uniformly
controlled implementation: a conditional expectation over counterfactual
histories can demand genuine coin flips that the original run never made.
A bounded bias guarantee also does not control its derivative at the baseline.
No cost-preserving reduction of the full minimax class was obtained.

`fisher.py` and `fisher.json` provide nine deterministic finite-horizon
diagnostics, for 3--5 dyadic atoms and flip caps 256,512,1024. No random seed,
training data or held-out data is used. The extracted one-coin stopping
policies optimize a floating-point Fisher/work criterion on a known radial
submodel; normalized ratios range from 4.73941 to 6.19822. These tests provide
no support for an extra logarithmic loss along those particular directions.
They are not certified enclosures, unbounded-horizon optima, a uniform-in-scale
theorem, or an all-algorithm converse. A two-sided perturbation uses Q_(2rho),
as the positive direction leaves the baseline Q_rho boundary. The finite
derivative and exhaustive horizon-three checks are saved in the code.

## Primary-source comparison

`sources.md` identifies the actual statements and access limits. The
finite-gap entropy mechanism overlaps Chen--Li--Qiao Lemma 4.1/Appendix D;
the note explicitly proves the needed Bernoulli and separated-gap variant.
Lee--Valiant's Section 7 fixes the two conditional laws and a per-coin cap;
its two average unbiasedness constraints cannot replace the present all-q
global-rarity requirement at fixed mu. Their broader information decomposition
remains relevant but does not supply the missing reduction here. The preceding
Giles--Haji-Ali and later adaptive-nested-simulation comparisons are retained
with their actual observation models. Farrell's original proof was not
accessible in this pass; only the identified restatements were inspected.
No predecessor being found in this targeted audit is a novelty certificate.

## Validation and exact remaining question

`BASELINE.md` and `BASELINE.json` distinguish old claims, exact formal scope,
current bytes and concurrent ownership. `validate.py` checks original locks,
preservation, all 34 current guard regressions, exact scalar constants, and a
fresh replay of all nine finite policies without overwriting published results.
Commands, exit statuses, source hashes and replay limits are in
`validation.json`. No new Lean target is accepted; previous unchanged
kernel evidence is reused. External-machine replay of this checkpoint is
unavailable. TeX compilation is recorded separately.

The precise remaining question is whether a nonlinear or genuinely interactive
known-mu, known-rho estimator can attain C Psi for this one quadratic law,
uniformly in rho and B, or whether a new converse can control those operations.
The additive lower theorem alone does not answer that question.
