# The hard-cap counterexamples: library audit

Section 5 of the hard-budget RMS note
([`research/2026-10-30-hard-budget-rms/NOTE.md`](../../research/2026-10-30-hard-budget-rms/NOTE.md))
shows that the independent timeout-fallback ladder of its reduction cannot be
weakened. At $\mu=\delta_{1/2}$ a fresh flip reveals an iid Bernoulli sign;
fix $\rho=1/4$. For dyadic $b\ge4$ a base takes $b/4$ fresh observations and
forms a clipped sample mean, and independently, with probability $p=1/8$,
requests $4b$ discarded observations. Its expected work is $3b/4\le b$ and its
uncapped MSE is at most $\min(\rho^2,4\rho/b)=K(b)^2$. A single cap at $4b$
with the midpoint on timeout has MSE $p(\rho/2)^2=\rho^2/32$, and reusing the
same delay bit at every stage keeps that floor, while the independent ladder
does not. The audited
[hard-budget record](../hard-budget-rms-20261104/README.md) proves the
reduction and its applications; these counterexamples were finite evidence
and paper arguments. Lean now checks them, in
[`lean/ThresholdHC/HardCapNecessity`](../../lean/ThresholdHC/HardCapNecessity/Full.lean).
The research package and the `HardBudget` group are unchanged. The audit runs
below were made at commit
[`315a162`](https://github.com/davidiach/adaptive-threshold-estimation/commit/315a162).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/HardCapNecessity/Specification.lean)
defines the endpoint gap `halfGap`, the all-negative sign law `zeroSigns`
($\theta=0$), the rate $K(b)=\min(\rho,2\sqrt{\rho/b})$ at $\rho=1/4$
(`rareRate`), and `RarePremise`, the stage premise of
`HardBudget.ObservableFallbackStatement` with $M=\rho=1/4$, $C=1$ and $f=K$,
uniformly over every rare sign law at $\delta_{1/2}$.

| Target | Statement |
|---|---|
| `rare_rate` | $K$ meets the rate hypotheses of the fallback reduction with $M=1/4$, and for every $C$ there is $B_0\ge4$ with $32C^2K(B)^2<1/512$ for all $B\ge B_0$. |
| `hard_cap_necessity` | One base family with one seed law at every stage meets `RarePremise`. With independent stages the fallback controller keeps the cap $\lfloor B\rfloor$ and the last-success output, and for $B\ge4$ and every rare sign law has squared risk at most $32K(B)^2$. A controller that feeds one seed to every stage keeps the cap and the last-success output on the constant seed array. Every estimator with that seed law and the shared-seed ladder output (at any depth), and every estimator with the stage seed law and the output of one capped run of stage $j\ge2$ (cap $4\cdot2^j$) with the midpoint on timeout, has squared risk at least $\rho^2/32=1/512$ at $\theta=0$. |

The floors are stated for every estimator with the pinned seed law and
output, not only for the constructed witnesses, and they are lower bounds
rather than the note's exact values $p(\rho/2)^2$ and $(\rho/2)^2p^{m-1}$. The
independent controller is given the general reduction's bound $32K(B)^2$, not
its exact MSE. Nothing is claimed about the general functional
$\mathcal K_{\mu,\rho}$, only about the explicit $K$ at $\rho=1/4$. The
shared-seed stages read disjoint coin labels: restarts on unused flips of the
same hidden coin are not formalized separately.

## How the proofs go

- [`Rate.lean`](../../lean/ThresholdHC/HardCapNecessity/Rate.lean): the rate
  identities and $K(B)^2\le1/B$.
- [`Fresh.lean`](../../lean/ThresholdHC/HardCapNecessity/Fresh.lean): the
  clipped mean of $N$ fresh flips and its delayed form, which buys more flips
  after the ones it reads and returns the same value; exact work, and squared
  risk at most $\min(1/16,1/(4N))$ at the endpoint gap.
- [`Base.lean`](../../lean/ThresholdHC/HardCapNecessity/Base.lean): the base
  family behind a delay coin of probability $1/8$ (midpoint at stages $0,1$;
  $2^i$ flips, or $17\cdot2^i$ on the delay bit, at stage $i+2$), and the
  premise.
- [`Controllers.lean`](../../lean/ThresholdHC/HardCapNecessity/Controllers.lean):
  the shared-seed and single-fallback controllers; on the delay bit every
  stage of index at least two times out at its cap $16\cdot2^i<17\cdot2^i$, so
  the output is the midpoint $1/8$ on a seed set of probability $1/8$, which
  gives $(1/8)(1/8)^2=1/512$.
- [`Full.lean`](../../lean/ThresholdHC/HardCapNecessity/Full.lean): the
  independent controller from `HardBudget.observable_fallback`.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_hard_cap_necessity.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components) and 65 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [hard-cap-necessity-audit.log](hard-cap-necessity-audit.log) |
| `python -m unittest discover -s tools -p 'test_hard_cap_necessity.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,130 constants (15,412 theorems) in 1,612 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,572 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,613 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 16
entries to `tools/definition_lock.json`: the two statements, `RarePremise`,
`rareRate`, `halfGap`, `zeroSigns`, the fresh and delayed estimators, the
base family with its seed law and match helper, and the two controllers. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The package's finite recurrence and
schedule audits remain finite evidence.

## Review

The item was planned by one agent and criticized by a second, which asked for
the floors to be stated for every estimator with the pinned seed law and
output, at every ladder depth, rather than for the prover's own witness. A
third agent wrote the proofs. Before the specification was pinned, a fourth
agent that had not written them rebuilt the modules, printed the axioms,
checked the specification against the critic's text, and checked the
construction against the note: stage $i+2$ reads $2^i$ flips, the delay branch
buys $17\cdot2^i$ and times out at the cap $16\cdot2^i$, the expected work is
$3\cdot2^i\le b$, and the zero sign law is rare. It found no defect in the
Lean; its two minor points concerned docstrings (the shared seed law and the
order of the discarded flips, and the conditions $B\ge4$ and $j\ge2$), which
were corrected before the pin. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
