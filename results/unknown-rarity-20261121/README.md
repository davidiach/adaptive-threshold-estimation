# The obstruction to uniform adaptation to unknown rarity: library audit

[`docs/process/TRACK_D.md`](../../docs/process/TRACK_D.md#an-obstruction-to-completely-uniform-adaptation-to-unknown-rarity)
fixes a known gap $0<d<1/2$ and a budget-indexed family of estimators $A_B$
that does not receive the rarity bound $\rho$ and stops almost surely at every
constant positive-sign prior $\theta\in[0,1/4]$. Even with interleaving and
adaptive coin creation, no single finite $C$ gives

$$\sup_{0\le\theta\le\rho}\bigl(\mathbb E_\theta(\hat\theta_B-\theta)^2\bigr)^{1/2}\le C\min\Bigl\{\rho,\frac{\sqrt\rho}{d\sqrt B}\Bigr\}$$

for every budget and every $\rho\in(0,1/4]$; expected-work bounds imply the
stopping premise, so they cannot circumvent it. The note marks the proof as
not Lean-checked, and the results guide and
[`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md#2-unknown-rarity)
retained it as a paper proof. Lean now checks it, in
[`lean/ThresholdHC/UnknownRarity`](../../lean/ThresholdHC/UnknownRarity/Full.lean).
The process note is unchanged. The audit runs below were made at commit
[`2aae4e7`](https://github.com/davidiach/adaptive-threshold-estimation/commit/2aae4e7).

## Statements

The model is the Tier 6 adaptive experiment at the gap law `Measure.dirac d`:
every fresh coin has gap $d$, the seed space is an arbitrary measurable space,
and the policy may interleave observations and create coins adaptively. The
RMS error is the extended-real `rootMeanRisk`, so infinite risk is kept; its
target $\theta$ equals the sign mean of `constantPrior θ` by
`StoppingProgram.constantPrior_mean`. Quantifier order encodes that the family
does not receive $\rho$.
[`Specification.lean`](../../lean/ThresholdHC/UnknownRarity/Specification.lean)
states:

| Target | Statement |
|---|---|
| `unknown_rarity_obstruction` | The source claim: for $d<1/2$, every real $C$ and every family $A_B$ ($B\ge1$) on arbitrary seed spaces that stops almost surely at every constant prior $\theta\in[0,1/4]$, the bound above fails for some $B\ge1$, $\rho\in(0,1/4]$ and $\theta\le\rho$. |
| `expected_work_obstruction` | The source remark: the same with the stopping premise replaced by finite expected work at every constant prior in $[0,1/4]$. |
| `stopped_transcript_ac` | The absolute continuity the proof uses: at $d<1/2$, if the estimator stops almost surely under a sign law $v$, the law of seed and tape under $v$ is absolutely continuous with respect to its law under any sign law $q$. |
| `fixed_budget_obstruction` | Beyond the source: one estimator, one budget $B>4C^2/d^2$, stopping almost surely only at $\theta=1/4$; the bound fails for some $\rho\in(0,1/4]$ and $\theta\le\rho$. |

A negative $C$ only strengthens the claims, since `ENNReal.ofReal` clips the
bound to zero. The budget index is real. The absolute continuity is stated in
the direction used and for the image of the seed and tape.

## How the proofs go

- [`Transfer.lean`](../../lean/ThresholdHC/UnknownRarity/Transfer.lean)
  generalizes the stopping-event argument of `NonnegativeUnbiased` to an
  arbitrary measurable set of seed–tape pairs: at interior gaps every prior in
  $[0,1]$ gives the same finite transcripts positive probability, the gap is
  almost surely $d$ under the seed law of `dirac d`, and almost-sure stopping
  makes the countable union over stopped transcripts exhaust the space. So a
  null set under one sign law is null under one at which the estimator stops.
- [`Risk.lean`](../../lean/ThresholdHC/UnknownRarity/Risk.lean): an RMS bound
  that is linear in $\rho$ for every small $\rho$ forces zero risk, zero RMS
  forces zero output almost surely, and the bound at $\rho=1/4$ is below $1/4$
  once $B>4C^2/d^2$.
- [`Obstruction.lean`](../../lean/ThresholdHC/UnknownRarity/Obstruction.lean):
  zero output at $\theta=0$ transfers to $\theta=1/4$, where the RMS error is
  $1/4$; the family form takes $B=\max\{1,4C^2/d^2+1\}$, and the expected-work
  form goes through `Tier5.creation_stops`.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_unknown_rarity.py --replay --jobs 2` | 7 exact statements (the 4 targets and 3 components) and 26 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [unknown-rarity-audit.log](unknown-rarity-audit.log) |
| `python -m unittest discover -s tools -p 'test_unknown_rarity.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,037 constants (15,338 theorems) in 1,606 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,556 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,607 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 5
entries to `tools/definition_lock.json`: the four statements and the event
indicator `setEvent`. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. As the source says, the obstruction
does not rule out an additive error floor, a positive lower bound on rarity,
restricted parameter ranges or an algorithm given $\rho$; the checked
adaptation controller receives $\rho$ and is not affected.

## Review

The item was planned by one agent and criticized by a second, which kept the
statements, replaced the planned likelihood-ratio route by the template of the
checked nonnegativity obstruction, and asked for an explicit limit step at
$\theta=0$ and for the fixed-budget form and the absolute continuity to be
marked as going beyond the source. A third agent wrote the proofs. Before the
specification was pinned, a fourth agent that had not written them rebuilt the
modules (byte-identical outputs), printed the axioms, restated the main target
from the critic's text, and checked non-vacuity: the immediate-stop estimator
meets both premises, and at $d=1/4$, $C=1$, $B=1\le4C^2/d^2$ the zero
estimator meets the bound for every $\rho$ and $\theta$, so the threshold
$B>4C^2/d^2$ is needed. It found no defect; its one minor point concerned the
implementer's notes. These were reviews by AI agents, not a specialist referee
report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
