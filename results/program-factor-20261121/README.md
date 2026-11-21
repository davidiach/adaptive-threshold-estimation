# The stopping-program factor $3\sqrt7/2$: library audit

The first review of the rms-constants package
([`adaptive-threshold-math-review.tex`](../../research/2026-11-17-rms-constants/adaptive-threshold-math-review.tex),
the page headed "A tighter certificate for minimax risk") states that in the
rare-event model the infinite stopping program satisfies

$$R\le P_\infty\le\tfrac{3\sqrt7}{2}R,\qquad \tfrac{3\sqrt7}{2}\approx3.969,$$

where $R$ is the minimax RMS risk under an expected budget $B$. The checked
factor was $8$ ([`infinite_program_comparison`](../../lean/ThresholdHC/Genie/InfiniteComparison.lean)).
With the checked cap comparison this gives $R\le P_N\le3\sqrt7\,R<8R$ whenever
$N\ge4B/9$, and the same factor for any verified feasible upper bound $U$ and
genie lower bound $L$ with $U\le2L$. These had a paper proof with exact
arithmetic only. Lean now checks them, in
[`lean/ThresholdHC/ProgramFactor`](../../lean/ThresholdHC/ProgramFactor/Full.lean).
The research package and the `Genie` and `SquareRootCap` groups are unchanged.
The audit runs below were made at commit
[`ddff9de`](https://github.com/davidiach/adaptive-threshold-estimation/commit/ddff9de).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/ProgramFactor/Specification.lean)
states four targets, for every probability law of gaps, $0<\rho\le1/2$ and
$B>0$, against the existing `rareMinimaxRisk`, `infiniteProgramValue`,
`programValue` and `genieValue`.

| Target | Statement |
|---|---|
| `infinite_program_factor` | $R\le P_\infty\le(3\sqrt7/2)\,R$. |
| `four_ninths_factor` | For every cap $N\ge4B/9$: $R\le P_N\le3\sqrt7\,R$. |
| `genie_test_factor` | For every cap $N>0$ and all $U\ge P_N$ and $L\le G_N$ with $U\le2L$: $R\le U\le3\sqrt7\,R$. |
| `below_eight` | $3\sqrt7\,R<8R$. |

The cap condition $N\ge\lceil4B/9\rceil$ is written $4B/9\le N$ for a natural
$N$, which is equivalent. The genie test is stated for arbitrary bounds $U$
and $L$, as in the paper's sentence; taking $U=P_N$ and $L=G_N$ gives the
factor-two test of the `Genie` group. `below_eight` uses $0<R<\infty$, which
the proof derives from the existing genie and program bounds.

## How the proofs go

The factor $8$ of the checked route has two sources: the prefix-pair modulus
$3/8$ and an absorption into the variance and work references at the fixed
weight $1/3$, which loses a factor two through $(\sqrt x+\sqrt y)^2\ge x+y$.
Tuning that weight alone gives about $3\sqrt{13}/2\approx5.41$, so the proof
replaces the local inequality.

- [`Absorption.lean`](../../lean/ThresholdHC/ProgramFactor/Absorption.lean):
  each endpoint $q$ of a four-prior quartet keeps weight $a$ and gives $1-a$
  to the midpoint of the two reference priors. With
  $(\sqrt x-\sqrt y)^2\le(x-y)^2/(4c)$ for $x,y\ge c>0$, the stopped Hellinger
  distance of the new endpoints is at most $a^2K/(2(1-a)^2)$ times the work
  under the new midpoint, where $K$ is the information/work ratio. A finite
  ratio forces zero contrast on every null reference prefix.
- [`Population.lean`](../../lean/ThresholdHC/ProgramFactor/Population.lean)
  restates the population and observable chain of the factor-8 route once,
  with the local bound as a hypothesis, and instantiates it.
- [`Modulus.lean`](../../lean/ThresholdHC/ProgramFactor/Modulus.lean) picks
  $a=1/(1+\sqrt{3x/2})$ for $x=BK>0$ and $a=1/2$ for $x=0$; the remaining
  scalar inequality is $(2/3)(s-6)^2\ge0$. With the attained four-prior
  duality at each finite cap and prefix truncation, as in the factor-8 proof,
  this gives $P_\infty\le(3\sqrt7/2)R$.
- [`Full.lean`](../../lean/ThresholdHC/ProgramFactor/Full.lean) combines it
  with the checked lower half $R\le P_\infty$, the cap comparison
  $P_N\le2G_N$ for $N\ge4B/9$ and $G_N\le P_\infty$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_program_factor.py --replay --jobs 3` | 7 exact statements (the 4 targets and 3 components) and 37 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [program-factor-audit.log](program-factor-audit.log) |
| `python -m unittest discover -s tools -p 'test_program_factor.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,503 constants (14,074 theorems) in 1,503 modules, same axioms. 147 exported instances. 3,289 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,504 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added six
entries to `tools/definition_lock.json`: `weightedLow`, `weightedHigh` and the
four statements. No existing entry changed. The run recorded here is a later
one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. Whether $3\sqrt7/2$ is optimal is not claimed.
The research package, which calls the bound a paper proof, describes its own
checkpoint and is unchanged.

## Review

The group was planned by one agent, criticized by a second, which replaced the
specialized genie test by the general $U$, $L$ form and checked the
mathematics, and written by a third. Before the specification was pinned, a
fourth agent that had not written the proofs rebuilt the modules, replayed
them through the kernel checker, restated the targets, printed the axioms,
ran the audit's scans and probed non-vacuity: $0<R<\infty$ on every
admissible instance, the genie-test hypotheses are satisfiable at every cap
$N\ge4B/9$, and $3\sqrt7/2<8$. It found four minor points: the source's
"$<8R$" was not stated, one module docstring reversed the mixing-weight
convention, one docstring described a proof step instead of its conclusion,
and the plan's description of the genie test was stale. The first became the
target `below_eight`, from the reviewer's probe; the docstrings were reworded
before this audit. These were reviews by AI agents, not a specialist referee
report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
