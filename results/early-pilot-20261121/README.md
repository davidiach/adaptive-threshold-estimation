# The early-stopping pilot of the arbitrary-law adaptation: library audit

The learning stage of the arbitrary-law adaptation appendix
([`paper/v6/arbitrary-law-adaptation.tex`](../../paper/v6/arbitrary-law-adaptation.tex),
the same text in [`docs/ARBITRARY_LAW_ADAPTATION.md`](../../docs/ARBITRARY_LAW_ADAPTATION.md))
buys a capped multi-depth pilot: at each depth $j$, $m$ probes, each stopping
on its first unresolved coin, after $M$ completed coins, or after $b_j$ flips.
The paper remarks that the coin cap $M$ makes easy-law pilots stop without
spending all their authorized flips. The Lean pilot reads every block in full,
so it is charged its cap, and the guides record that the remark is not
formalized ([`docs/ARBITRARY_LAW_FORMALIZATION.md`](../../docs/ARBITRARY_LAW_FORMALIZATION.md)).
Lean now checks a pilot whose probes stop once decided, in
[`lean/ThresholdHC/EarlyPilot`](../../lean/ThresholdHC/EarlyPilot/Full.lean).
The paper gives no quantitative bound; the bounds below are derived here. The
paper is unchanged. The audit runs below were made at commit
[`8be354a`](https://github.com/davidiach/adaptive-threshold-estimation/commit/8be354a).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/EarlyPilot/Specification.lean)
defines `IsEarlyPilot J m ρ A` for a family of adaptive estimators indexed by
the depth: all share one policy with the pathwise cap of the pilot, buy on
every table exactly the probes' flips $\sum_{j<J}\sum_{k<m}$`probeFlips`, and
output at index $i<J$ the full pilot's certificate (the upper median of the
probes of depth $i+1$).

| Target | Statement |
|---|---|
| `early_pilot_exists` | For all $J$, $m>0$ and $\rho>0$ there is a family with `IsEarlyPilot J m ρ`. |
| `early_pilot_event` | For every such family, probability gap law, sign law and index: if $J\ge1$, $\varepsilon>0$ and $8\log(2J/\varepsilon)\le m$, then with probability at least $1-\varepsilon$ under the original experiment, every certificate $i<J$ lies between $\mu(d\le2^{-(i+1)})$ and the pilot bound (the event (A8)). |
| `early_pilot_work` | Its expected work is at most $m\sum_{j<J}\min\{b_{j+1},\,M\int W_{j+1}\,d\mu\}$, with $W$ the work envelope. |
| `easy_law_work` | If every gap is at least $a>0$, the expected work is at most $512\,mMJ(J+3)/a^2$. |
| `easy_law_vanishing` | For $a,\rho,\varepsilon>0$ there is $J_0$ such that for every law with gaps at least $a$ and every $J\ge J_0$, the expected work is at most $\varepsilon$ times the cap $m\sum_jb_j$. |

The event, work and easy-law statements are conditional on `IsEarlyPilot`;
they have content because the existence statement inhabits it. The early
pilot stands alone: it is not installed in the learning stage, so the stage
results still charge the full pilot. The finer per-probe cap
$\min(b_j,M4^j)$ is not stated for arbitrary admissible paths.

## How the proofs go

- [`VarReader.lean`](../../lean/ThresholdHC/EarlyPilot/VarReader.lean) and
  [`Estimator.lean`](../../lean/ThresholdHC/EarlyPilot/Estimator.lean): one
  variable-length reader runs the $Jm$ probes in order and stops each once it
  is decided; a one-flip invariant identifies its outputs and work with those
  of the probes on every table.
- [`ProbeStop.lean`](../../lean/ThresholdHC/EarlyPilot/ProbeStop.lean) and
  [`Law.lean`](../../lean/ThresholdHC/EarlyPilot/Law.lean): the event transfers
  from the coin array to the original experiment as for the full pilot; the
  probe's charge is at most $\min(b,\text{work of the first }M\text{ coins})$, whose
  mean on fresh coins is at most $\min(b,MW)$.
- [`Easy.lean`](../../lean/ThresholdHC/EarlyPilot/Easy.lean): with gaps at
  least $a$ the envelope of depth $j+1$ is at most $1024(j+2)/a^2$; the coin
  cap is at most $(\sqrt{64/\rho}+1)2^J$ and the cap of the pilot at least
  $m4^J/2$ for $J\ge1$, so the ratio vanishes once $J^2/2^J$ is small.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_early_pilot.py --replay --jobs 2` | 8 exact statements (the 5 targets and 3 components) and 78 transitive axiom reports over the 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [early-pilot-audit.log](early-pilot-audit.log) |
| `python -m unittest discover -s tools -p 'test_early_pilot.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,554 constants (17,480 theorems) in 1,755 modules, same axioms. 160 exported instances, the new one the `SizeOf` instance Lean generates for the reader's state structure; 6 registered orphans, unchanged. 3,916 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,756 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 39
entries to `tools/definition_lock.json`: the five statements, the predicate,
and the reader, its state and the probe definitions. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which renamed
the predicate, asked for the vanishing statement in a form uniform over the
gap law and required the existence statement to be pinned beside the
conditional ones. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them rebuilt the modules, printed
the axioms and checked the statements against the source. It found no defect
in the Lean. Its three minor points concerned docstrings: one comparison with
the cap that fails at $J=0$, a module docstring that described results of
another module, and one that called an upper bound the probe's charge. All
were corrected before the pin. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
