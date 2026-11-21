# The weighted sign entropy with coefficient 214: library audit

Lemma `lem:weighted-sign` of the v6 lower-bound foundations appendix
([`paper/v6/appendix-lower-foundations.tex`](../../paper/v6/appendix-lower-foundations.tex),
display `eq:sc-weighted-sign`) bounds the entropy of any weight vector by the
expected work of one observable sign test that serves several gaps:
$1+\mathrm{Ent}(\pi)\le214\sum_j\pi_jc_j$ with $c_j=d_j^2\,\mathbb E_{-d_j}\tau$.
The frozen target `EntropyTailLower.WeightedSignEntropyStatement` states the
same inequality with the weaker coefficient 4096
([proof map](../../docs/ENTROPY_TAIL_LOWER_PROGRESS.md)), deliberately, and
the paper's 214 was not Lean-checked. Lean now checks it, in
[`lean/ThresholdHC/WeightedSignSharp`](../../lean/ThresholdHC/WeightedSignSharp/Full.lean).
The frozen target and the paper are unchanged. The audit runs below were made
at commit
[`e9dfdb2`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e9dfdb2).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/WeightedSignSharp/Specification.lean)
holds three statements about one observable sign test with a common seed law.
Its work $c_j$ is the actual negative-sign work at gap $d_j$, and the gaps
satisfy $0<d_j\le1/128$ with $2d_{j+1}\le d_j$.

| Target | Statement |
|---|---|
| `sign_work_floor` | If the negative-sign work is finite and the test errs with probability at most $1/10$ under both signs, then $3/40<d^2\,\mathbb E_{-d}\tau$. |
| `window_overlap` | On every path, $\sum_j\mathbf 1_{E_j}/(1+c_j)\le25/3$ for the stopping windows $E_j$. |
| `weighted_sign_entropy_214` | With the binders of the frozen 4096 target (finite negative-sign work at every gap, errors at most $1/10$, nonnegative weights $a$): `costEntropy a` $\le214\sum_ja_jc_j$. |

The homogeneous form for every nonnegative weight vector is equivalent to
the paper's display for probability vectors, with zero weights allowed. Only
finite negative-sign work is assumed, weaker than the paper's finite
expectation under both signs, and nothing is assumed under the fair coin. The
windows are the library's, with upper time $\lceil4\,\mathbb E\tau\rceil+1$ in place
of the paper's $\lceil4\,\mathbb E\tau\rceil$, so they are at least as large.
No Lean theorem consumes the 214: the headline coefficient $10^{-17}$ is
proved by other routes. The $\Psi$-gap constant and the entropy-tail law
constants that the paper derives from this lemma are not restated.

## How the proofs go

- [`CappedSign.lean`](../../lean/ThresholdHC/WeightedSignSharp/CappedSign.lean):
  the test stopped at $N=\lceil10\,\mathbb E_-\tau\rceil+1$ as a legal procedure.
- [`SignFloor.lean`](../../lean/ThresholdHC/WeightedSignSharp/SignFloor.lean):
  Markov's inequality gives negative-law mass at least $4/5$ on the capped
  event where the test answers negative, whose positive-law mass is at most
  $1/10$; data processing, the stopped chain rule `PsiNull.capped_transcript_kl`
  and $\mathrm{kl}(4/5,1/10)\ge(9/5)\log2$ give $d^2\,\mathbb E\tau\ge0.0779>3/40$. The
  paper reaches the same constant by letting the cap tend to infinity.
- [`SharpOverlap.lean`](../../lean/ThresholdHC/WeightedSignSharp/SharpOverlap.lean):
  the per-window weight is at most $\min(1,4^7\cdot4^{-k})$, which sums to at
  most $25/3$.
- [`Full.lean`](../../lean/ThresholdHC/WeightedSignSharp/Full.lean): the
  assembly with $\log(25/3)\le87/40$ and $149\cdot3/40=9+87/40$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_weighted_sign_sharp.py --replay --jobs 2` | 6 exact statements (the 3 targets and 3 components) and 26 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [weighted-sign-sharp-audit.log](weighted-sign-sharp-audit.log) |
| `python -m unittest discover -s tools -p 'test_weighted_sign_sharp.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,221 constants (17,231 theorems) in 1,733 modules, same axioms. 156 exported instances; 6 registered orphans, unchanged. 3,837 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,734 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 6
entries to `tools/definition_lock.json`: the three statements and the capped
test's cost, procedure and event. No existing entry changed. The run recorded
here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which kept the
statements and moved the proof-only imports out of the specification. A third
agent wrote the proofs. Before the specification was pinned, a fourth agent
that had not written them:
- rebuilt the modules, found the compiled files byte-identical to the implementer's, and printed the axioms;
- checked the sign convention, the gap condition and the homogeneous form against the paper, and proved in Lean that the 214 statement implies the frozen 4096 one;
- checked that infinite work gives an empty window, so no junk value enters the overlap statement.

It found no defect in the Lean. Its one minor point concerned the location of
the implementer's report. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
