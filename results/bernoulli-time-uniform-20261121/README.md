# The Bernoulli-subfamily time-uniform lower bound: library audit

The unknown-law confidence note
([`docs/UNKNOWN_LAW_CONFIDENCE.md`](../../docs/UNKNOWN_LAW_CONFIDENCE.md#a-time-uniform-lower-bound-in-the-original-experiment))
proves a time-uniform lower bound in the original experiment: if a
deterministic nonincreasing envelope $t$ bounds the half-width of an online
interval on a joint event of simultaneous coverage and width with probability
at least $1-\delta$, then
$t(n)\ge\sqrt{3(1-\delta)\rho/64}\,\sqrt{\log\log n/n}$ for infinitely many
$n$. Its proof restricts to constant sign laws in $[\rho/2,\rho]$, simulates
the experiment from an iid Bernoulli stream and applies Duchi and Haque's
Proposition 11 as a cited result. The note and the secondary-claims guide kept
this coefficient as a paper proof
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md)). Lean now checks
it, in
[`lean/ThresholdHC/BernoulliTimeUniform`](../../lean/ThresholdHC/BernoulliTimeUniform/Full.lean).
The paper is unchanged. The audit runs below were made at commit
[`3a577bc`](https://github.com/davidiach/adaptive-threshold-estimation/commit/3a577bc).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/BernoulliTimeUniform/Specification.lean)
states both targets in the original hidden-gap online experiment, for one
adaptive controller with its private seed law.

| Target | Statement |
|---|---|
| `constant_prior_prefix_kl` | For every gap law, controller, $0<\theta,\theta'<1$ and $n$: the KL divergence between the observable prefix laws (the seed and the first $n$ flips) of the constant sign laws $\theta'$ and $\theta$ is at most $n(\theta'-\theta)^2/[\theta(1-\theta)]$. |
| `bernoulli_time_uniform_lower` | For every gap law, $0<\rho\le1/4$, $0<\delta<1$, controller and measurable interval endpoints $L,U$: if `OnlineIntervalCoverage μ A L U ρ δ t` holds (for every sign law of mean at most $\rho$, simultaneous coverage and $U-L\le2t(n)$ at every $n$ on one event of probability at least $1-\delta$), then for every $M$ some $n\ge\max(M,3)$ has $\sqrt{3(1-\delta)\rho/64}\,\sqrt{\log\log n/n}\le t(n)$. |

The envelope need not be nonincreasing, so the statement is stronger than the
note's on that point. The hypothesis $0<\delta$ is kept as in the note; the
proof does not use it. For $n\ge3$ both square roots are of positive numbers,
so neither side is a junk value. The coverage hypothesis is the one of the
law-dependent lower bound `law_dependent_interval_lower`, which gives the
universal multiple $10^{-22}$ of the known-law rate; the two bounds are
separate statements.

## How the proofs go

The Lean proof does not simulate an iid stream and does not use the cited
proposition.

- [`TranscriptKL.lean`](../../lean/ThresholdHC/BernoulliTimeUniform/TranscriptKL.lean):
  for a fixed seed and gap array, the KL divergence between the finite
  transcript laws of two constant sign laws splits into one term per queried
  coin. Each term is at most the chi-square divergence times the coin's visit
  mass, and the visit masses sum to at most $n$.
- [`PrefixKL.lean`](../../lean/ThresholdHC/BernoulliTimeUniform/PrefixKL.lean):
  the per-seed bound passes to the observable prefix law through the realized
  kernel of the experiment, as for the tail prefix bound of the law-dependent
  lower bound.
- [`Testing.lean`](../../lean/ThresholdHC/BernoulliTimeUniform/Testing.lean):
  a first-crossing test with threshold $2a/3$ for every $\delta<1$ (the
  existing lemmas hard-code $\delta\le1/2$): if the observable KL of the
  alternatives is not summable in the testing sense, the half-width is at
  least a third of the displacement infinitely often.
- [`Schedule.lean`](../../lean/ThresholdHC/BernoulliTimeUniform/Schedule.lean)
  and [`Full.lean`](../../lean/ThresholdHC/BernoulliTimeUniform/Full.lean): the
  base law $3\rho/4$ and the alternatives $3\rho/4+\rho/(4\cdot3^k)$, all of
  mean at most $\rho$, at geometric budgets $N_k$. The base variance satisfies
  $\theta(1-\theta)\ge39\rho/64$; the slack between $39/576$ and the stated
  $27/576=3/64$ absorbs the rounding of $N_k$ and the drift of
  $\log\log N_k$, so the bound holds at all large $k$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_bernoulli_time_uniform.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components) and 44 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [bernoulli-time-uniform-audit.log](bernoulli-time-uniform-audit.log) |
| `python -m unittest discover -s tools -p 'test_bernoulli_time_uniform.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,624 constants (17,543 theorems) in 1,761 modules, same axioms. 160 exported instances, unchanged; 6 registered orphans, unchanged. 3,923 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,762 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 7
entries to `tools/definition_lock.json`: the two statements and five
proof-internal definitions (the displacement, the base variance, the scaled
displacement, the budget schedule and the test events). No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which found the
statements faithful and the hypothesis class nonempty, and required no
correction. It pointed out that the existing first-crossing lemmas hard-code
$\delta\le1/2$ and need copies for $\delta<1$, and that the final slack is
tight, so the absorption must use large budgets. A third agent wrote the
proofs. Before the specification was pinned, a fourth agent that had not
written them:
- rebuilt the modules and printed the axioms of all 44 declarations;
- checked the statements token for token against the plan and the note;
- proved in Lean that the hypotheses are satisfiable ($L=0$, $U=1$, $t\equiv1/2$) and instantiated the main theorem with them.

It found no defect in the Lean. Its two minor points concerned the location of
the implementer's report and a docstring that called the prefix bound a bound
for every private seed, while it bounds the seed-averaged law; the docstring
was corrected before the pin. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
