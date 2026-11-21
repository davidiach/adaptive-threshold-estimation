# The restricted pilot correction: library audit

The upper-bound note of the population-step package
([`research/2026-10-27-population-step/upper/proof.tex`](../../research/2026-10-27-population-step/upper/proof.tex),
paragraph `Experiment`, Theorem `thm:saddle` and the unlabeled theorem after
it) fixes unbiased features $Y$ and $Z$ of one fresh coin, with
$\mathbb E_qY=\theta(q)$, $\mathbb E_qZ=0$ and $\mathbb E_qZ^2=v>0$ on the
rarity polytope $Q=\{q\in[0,1]^k:\sum_i\pi_iq_i\le\rho\}$. The map
$f(\beta,q)=\operatorname{Var}_q(Y-\beta Z)$ has a saddle point, so one fixed
coefficient $\beta_0$ gives an unbiased raw average with worst mean squared
error $F^*/n$, $F^*=\inf_\beta\sup_qf$, and no coefficient chosen by an
independent pilot does better. The secondary-claims guide retained this as a
paper proof
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md#4-population-step-auxiliary-claims)).
Lean now checks it, in
[`lean/ThresholdHC/PilotCorrection`](../../lean/ThresholdHC/PilotCorrection/Full.lean).
The research package is unchanged. The audit runs below were made at commit
[`e329470`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e329470).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/PilotCorrection/Specification.lean)
defines the polytope `rarityPolytope`, the sign mass $\theta(q)$, the law
`coinLaw` of one fresh coin's observations as the mixture over gaps and signs
of conditional laws `Pplus i` and `Pminus i`, the raw production average, its
fixed-coefficient and pilot mean squared errors (lower integrals in
$[0,\infty]$), and the hypotheses `FixedFeatures`.

| Target | Statement |
|---|---|
| `saddle` | `thm:saddle`: under `FixedFeatures`, $f(\beta,q)=\operatorname{Var}_q(Y-\beta Z)$ has a saddle point $(\beta_0,q_0)$ on $\mathbb R\times Q$, and both $\inf_\beta\sup_qf$ and $\sup_q\inf_\beta f$ (in the extended reals) equal $f(\beta_0,q_0)$. |
| `pilot_no_gain` | The pilot theorem: there are $\beta_0$ and $F^*=\inf_\beta\sup_qf$, chosen before $n$, such that for every $n\ge1$ the raw average with $\beta_0$ is unbiased on $Q$ with worst mean squared error exactly $F^*/n$, and for every pilot transcript space $T$, pilot laws $L_q$ (which may depend on $q$ arbitrarily) and measurable coefficient $\hat\beta$, independent of the $n$ production coins, the worst pilot mean squared error is at least $F^*/n$. |
| `coin_witness` | Beyond the source, a nonvacuity witness: one gap $d=1/2$, where one flip reveals the sign, and an internal fair coin give features meeting `FixedFeatures` with $v=1$ for every $0<\rho\le1/2$, and some $q\in Q$ at which every coefficient has variance at least $\rho(1-\rho)>0$. |

The model is an abstract mixture: the source's single-coin observation rule
(gaps $0<d_i\le1/2$, flips with success probability $1/2+(2S-1)D$) is replaced
by arbitrary conditional laws of one coin's observations and internal
randomization, which every observation rule induces; gaps and flips are not
modelled, and there is no formal link to the Tier 6 experiment. The side
conditions are weaker ($\pi_i\ge0$, $\rho\ge0$), measurability of $Y$, $Z$ and
$\hat\beta$ is assumed, and the observation and transcript spaces are in
universe zero. The work-accounting sentence ($\ell$ flips per coin, $m+n$
coins) is not modelled; since $\beta_0$ and $F^*$ are fixed before $n$, the
fixed clause at $m+n$ gives its arithmetic. `prop:two`, the specified pilot
implementation, the exact moment formulas and the example $427/16$ are not
stated. As in the source, clipping, adaptive features or sample sizes, bias
and nonlinear aggregation are outside the statements.

## How the proofs go

- [`Quadratic.lean`](../../lean/ThresholdHC/PilotCorrection/Quadratic.lean):
  a saddle point for $g(\beta,q)=A(q)-\theta(q)^2-2\beta c(q)+\beta^2v$ with
  $A$, $\theta$, $c$ affine on a compact convex set, found by maximizing
  $A-\theta^2-c^2/v$ and setting $\beta_0=c(q_0)/v$. This replaces the note's
  coercivity and active-set argument; the statement is unchanged.
- [`Mixture.lean`](../../lean/ThresholdHC/PilotCorrection/Mixture.lean): $Q$
  is compact, convex and nonempty, `coinLaw` is a probability law on $Q$, and
  integrals and variances under it are affine in $q$.
- [`Production.lean`](../../lean/ThresholdHC/PilotCorrection/Production.lean):
  the average of $n$ iid copies has mean $\mathbb EW$ and mean squared error
  $\operatorname{Var}W/n$; by Tonelli the pilot risk is the $L_q$-average of
  fixed-coefficient risks.
- [`Saddle.lean`](../../lean/ThresholdHC/PilotCorrection/Saddle.lean) and
  [`Full.lean`](../../lean/ThresholdHC/PilotCorrection/Full.lean): the saddle
  value; at $q_0$ every coefficient has variance at least $F^*$, so every
  pilot's risk at $q_0$ is at least $F^*/n$.
- [`CoinWitness.lean`](../../lean/ThresholdHC/PilotCorrection/CoinWitness.lean):
  the witness.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_pilot_correction.py --replay --jobs 2` | 6 exact statements (the 3 targets and 3 components) and 49 transitive axiom reports over the 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [pilot-correction-audit.log](pilot-correction-audit.log) |
| `python -m unittest discover -s tools -p 'test_pilot_correction.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,211 constants (15,482 theorems) in 1,619 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,583 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,620 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 11
entries to `tools/definition_lock.json`: the three statements,
`FixedFeatures`, `rarityPolytope`, `signMass`, `coinLaw`, `rawAverage`,
`fixedRisk`, `pilotRisk` and `fairCoin`. No existing entry changed. The run
recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. As the guide says, the result is not a
general prohibition on acquisition feedback or nonlinear estimators.

## Review

The item was planned by one agent and criticized by a second, which tied the
saddle statement's minimax values to $f(\beta_0,q_0)$, checked the
replacement saddle argument, and asked for the fair-coin witness because the
weakened side conditions allow $\rho=0$, where the no-gain bound says nothing.
A third agent wrote the proofs. Before the specification was pinned, a fourth
agent that had not written them rebuilt the modules, printed the axioms,
checked the specification against the plan and the critic's text, checked
that Mathlib's saddle-point predicate unfolds to the source's inequalities,
and fed `coin_witness` into `pilot_no_gain` to derive $F^*\ge\rho(1-\rho)>0$
with the pilot bound at every $n\ge1$. It found no defect in the Lean; its
three minor points concerned the docstring of `FixedFeatures`, an unrecorded
universe restriction and the implementer's notes, and the first two were
corrected before the pin. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
