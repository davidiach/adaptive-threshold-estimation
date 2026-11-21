# The bounded-depth obstruction, population half: library audit

Theorem `thm:cap` of the nonlinear-population upper note
([`research/2026-10-27-nonlinear-population/upper/proof-body.tex`](../../research/2026-10-27-nonlinear-population/upper/proof-body.tex),
lines 87–151; summarized in its
[final report](../../research/2026-10-27-nonlinear-population/FINAL_REPORT.md))
says that feedback does not repair bounded-depth nonidentifiability. For the
exact quadratic law and $K\ge1$ it builds an odd-Legendre pair of sign
profiles with separation $\Delta_K=\rho/((K+1)(2K+1))$ whose coin words of
length at most $2K$ all have the same probability; every population
procedure that uses at most $2K$ observations per coin, with arbitrary
pilots, interleaving and cross-coin feedback, then has the same transcript
law under both, so its worst RMS error is at least $\Delta_K/2$ whatever its
total work. The secondary-claims guide retained it as a paper proof
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md#5-nonlinear-feedback-depth-and-finite-approximation)).

Lean now checks the population half, the step from matching word
probabilities to equal transcript laws and the RMS floor, for every cap, gap
law and matching pair, in
[`lean/ThresholdHC/DepthObstruction`](../../lean/ThresholdHC/DepthObstruction/Full.lean).
The explicit Legendre pair, its separation $\Delta_K$ and the unrestricted
exit bound $p_K\ge1-4\varepsilon^2/\Delta_K^2$ are not yet stated; they remain
paper proofs. The research package is unchanged. The audit runs below were
made at commit
[`7249ded`](https://github.com/davidiach/adaptive-threshold-estimation/commit/7249ded).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/DepthObstruction/Specification.lean)
defines `PerCoinCap A N`: on every simulated population path of the
unchanged observable experiment, for every seed and every family of coin
tapes, every label receives at most $N$ flips. Matching word probabilities
through depth $N$ are `CapIdentification.OddMomentMatch`, which is equivalent
to them by `CapIdentification.odd_moments_iff_count_match`.

| Target | Statement |
|---|---|
| `capped_transcript` | For every gap law, sign laws $q_H,q_L$ with matching odd moments through depth $N$, and estimator with per-coin cap $N$, the joint laws of seed and full observed transcript under $q_H$ and $q_L$ are equal. |
| `equal_law_floor` | Equal seed-and-transcript laws give $\max(\mathrm{RMS}_H,\mathrm{RMS}_L)\ge|\theta_H-\theta_L|/2$, the last display of the proof, with infinite risk kept. |
| `population_cap_floor` | Lean-only extension, not a claim of the source: for every gap law and $\rho\ge0$, half the attained cap-$N$ diameter `capDiameter μ ρ N` floors the rare-prior RMS risk of every per-coin-capped procedure. It extends `CapIdentification.fixed_cap_identification` from single stopped procedures to arbitrary population feedback. |
| `history_cap_bridge` | The history-count cap used in `RestrictedRMS.three_flip_coefficient_iff`, with bound $N$, implies `PerCoinCap A N`. |

The conclusion of `capped_transcript` equates the whole seed-and-transcript
law, which is stronger than the source's finite-prefix equality, and needs no
almost-sure termination hypothesis: the output is a measurable function of
seed and transcript. `PerCoinCap` is deterministic, over every seed and tape
family; no almost-everywhere form is stated.

## How the proofs go

- [`CappedPath.lean`](../../lean/ThresholdHC/DepthObstruction/CappedPath.lean):
  under a per-coin cap, cutting every coin tape after $N$ flips leaves the
  population path unchanged.
- [`OneCoin.lean`](../../lean/ThresholdHC/DepthObstruction/OneCoin.lean): under
  matching odd moments, the completed length-$N$ prefix of one original coin
  tape has the same law under both sign laws.
- [`CappedTranscript.lean`](../../lean/ThresholdHC/DepthObstruction/CappedTranscript.lean):
  the observable law of a capped procedure depends only on the cut tapes, whose
  product laws agree.
- [`Floor.lean`](../../lean/ThresholdHC/DepthObstruction/Floor.lean): the two
  squared errors of one statistic against one law sum to at least
  $(a-b)^2/2$; the diameter floor uses `capDiameter_attained`.
- [`Bridge.lean`](../../lean/ThresholdHC/DepthObstruction/Bridge.lean): the
  history count bounds the simulated per-coin count.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_depth_obstruction.py --replay --jobs 2` | 7 exact statements (the 4 targets and 3 components) and 31 transitive axiom reports over the 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [depth-obstruction-audit.log](depth-obstruction-audit.log) |
| `python -m unittest discover -s tools -p 'test_depth_obstruction.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,255 constants (15,518 theorems) in 1,626 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,591 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,627 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 8
entries to `tools/definition_lock.json`: the four statements, `PerCoinCap`,
`capTapes`, the one-coin reader `readPrefix` and `historyCount`. No existing
entry changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The scoping critic split the item:
the Legendre and depth polynomials, the explicit pair under the quadratic law
with $\Delta_K$, and the exit bound (`thm:tail`) are a later group.

## Review

The item was planned by one agent and criticized by a second, which split
off the polynomial part and added the generic floor from equal laws, the
diameter extension and the bridge. A third agent wrote the proofs. Before the
specification was pinned, a fourth agent that had not written them rebuilt
the modules, printed the axioms, checked the statements against the critic's
text, and checked non-vacuity: an estimator that reads coin 0 $N$ times meets
the cap through the bridge, the cap binds (coin 0 is charged two flips under
cap two), and matching pairs with positive separation exist for laws with
infinite support. It found no defect. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
