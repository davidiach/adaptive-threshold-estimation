# Tier 5: unrestricted adaptive coin creation

The eight-hour-or-landmark goal began on 2026-10-27 at 08:19:16 UTC.
It extends the actual infinite-transcript information/work bound beyond the
fixed finite coin family of Tier 4. Earlier specifications and checkers remain
unchanged.

## Model and locked targets

Policies choose any natural-number coin label from the observed Boolean
history and a common random seed. A first observation of a label creates its
independent latent coin; later observations may revisit it in any order. There
is no allocation restriction or bound on the total number of labels. Magnitudes
and sign-prior perturbations may depend measurably on the common seed, allowing
arbitrary common random magnitude environments.

Each finite cylinder law is an explicit finite latent-sign mixture. Its cap is
computed from every label the finite decision tree can query, and may vary
without bound with the seed. Cap invariance and cylinder consistency must be
proved; they are not model assumptions. The realized-law condition identifies
bounded finite-prefix integrals and assumes no entropy or stopping conclusion.

The nine targets are normalization, cylinder consistency, actual finite-prefix
KL, plus-hypothesis halting from finite expected work, full KL as a prefix
supremum, the full information/work bound, its measurable-statistic corollary,
a realized unbounded fresh-coin example, and their combined theorem.
The example must have finite expected work but positive probability of
observing more than any prescribed number of distinct coins.

All three proof agents reviewed the statements before the 13-file
`TIER5_FROZEN.sha256` lock was created. The lock includes all prior lock manifests,
the specification's local import closure, the manifest, and the new verifier.

## New proof obligations

With unrestricted creation, finite expected work under the plus hypothesis
does not imply termination under the minus hypothesis. The new targets permit
minus-hypothesis nontermination. The entropy proof therefore uses generating
prefix sigma-algebras, convergence of conditional expectations of the
Radon--Nikodym derivative, and Fatou's lemma.

A separate likelihood comparison depends on the observation horizon rather
than the ambient number of coin labels: at horizon `n`, each direction of the
finite likelihood ratio is bounded by `(5/3)^n`. At most `n` distinct signs can
contribute; unused coins have likelihood factor one. This provides uniform
integrability bounds even when the seed-dependent finite cap is unbounded.

## Verification

The complete aggregate module `ThresholdHC.Tier5` builds. Its theorem
`tier5_landmark` combines all nine locked targets. The eight validation
regression tests pass. The first published foundation checkpoint, `199dcee`,
audited 25 declarations. The complete local audit now passes **9/9 targets and
109/109 declaration checks**, with all sources unchanged during verification.
The 13-file Tier 5 lock and every prior frozen file pass their hash checks.
Evidence is saved in `results/tier5_checkpoint_001.json` and
`results/tier5_audit_001.log`.

Independent Linux CI passed on proof commit
`bd446de9255fce6b7ea000cf44e933cd38733009` in
[run 40475536939](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40475536939).
It independently reports 9/9 Tier 5 targets and 109/109 declaration checks.
The same run also passes the original 121/121-point suite, the 713 theorem's
130 checks, Tier 3's 11 targets and 152 checks, Tier 4's 6 targets and 65 checks,
and the numerical and validation tests. The extracted CI evidence is stored in
`results/tier5_linux_checkpoint.json`.

The eight-hour-or-landmark goal reached its landmark in about 36 minutes:
all locked targets proved, independent final semantic reviews passed, standard
axioms only, earlier frozen results preserved, and Linux verification successful.

The main theorem proves, for the actual joint seed and infinite observation tape,

$$
D_{\mathrm{KL}}(P_T\Vert Q_T)
\le \frac{128}{225}h^2\,\mathbb E_P[W].
$$

The hypotheses are measurable policies and environments, the explicit realized
prefix laws, `0 < h`, `0 < d <= 1/2`, `0 <= eta <= 1/8`, and
`d * eta <= h/8` for every seed and coin. The locked theorem assumes finite
expected work under `P`; `creation_infinite_kl_bound_extended` also covers infinite
expected work using extended-real values. Every measurable statistic of the
joint transcript obeys the same bound by data processing.

The proof derives global absolute continuity from the stopped restrictions and
the `P`-almost-sure stopped cover. The minus law need not terminate. Generating
prefix sigma-algebras, conditional density convergence and Fatou then give
actual full KL equal to the supremum of prefix KL. Neither absolute continuity
nor entropy convergence is supplied as a hypothesis of the process theorem.

The nonvacuity example is a geometric stopping seed independent of countably
many Bernoulli signs. It observes a distinct new coin on every step. Both laws
realize the explicit model, expected work is finite, and every deterministic
creation bound is exceeded with positive probability.

This extends the information/work theorem. The prior 713 and other frozen
theorems retain their existing statements; Tier 5 does not silently change
their scope.

The theorem applies to any probability laws realizing the specified independent
latent-sign cylinders. Normalization and consistency are proved for every
admissible policy and environment. The concrete fresh-coin example proves
nonvacuity; constructing a canonical infinite process for every admissible
environment is not a target of this extension.

Two independent final reviews checked the exact combined theorem and the
finite/infinite bridges. They confirmed that the finite cap is derived per seed
and horizon, that density and absolute continuity are proved, that only `P`
stopping is used, and that the fresh-coin example has no deterministic creation
cap. Neither review found a substantive issue.

Run `python tools/verify_tier5.py --sequential --require-complete` to require
all nine targets. Partial checkpoints omit `--require-complete` and must report
pending targets explicitly. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed.
