# The pilot events (A8) and (A11) under the law of the whole learning stage: library audit

Displays (A8) and (A11) of
[`docs/ARBITRARY_LAW_ADAPTATION.md`](../../docs/ARBITRARY_LAW_ADAPTATION.md)
((UA8) and (UA11) of
[`paper/v6/arbitrary-law-adaptation.tex`](../../paper/v6/arbitrary-law-adaptation.tex),
subsection `sec:arbitrary-law-adaptation`) concern the capped multi-depth
pilot of the paid learning stage. With $m\ge8\log(2J/\varepsilon)$ probes at
every depth, with probability at least $1-\varepsilon$ its certificates
satisfy $F(2^{-j})\le U_j\le128(u_j+W_j/b_j+1/M)$ at every depth $j\le J$
and the learned law dominates the gap law; on the same event, for every
$J\ge J_0(\mu,\rho)$, the selection functional of the learned law is at most
$2^{24}$ times the oracle's.

The audited library proved both events for the stage on the coin array of the
original simulation law (`original_pilotStage_event`,
`original_pilotStage_oracle`), and the second without the two halves of (A8).
The formalization guide recorded that caveat
([`docs/ARBITRARY_LAW_FORMALIZATION.md`](../../docs/ARBITRARY_LAW_FORMALIZATION.md#learned-law-against-the-oracle-the-comparison)).
Lean now states both under the law of the original hidden-gap experiment of
the whole stage, in
[`lean/ThresholdHC/StagePilotLaw`](../../lean/ThresholdHC/StagePilotLaw/Full.lean).
The `ArbitraryLawAdaptation` group and the paper are unchanged. The audit runs
below were made at commit
[`b8e1efb`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b8e1efb).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/StagePilotLaw/Specification.lean)
states three targets for an arbitrary `LearnedStage` $S$ (private randomness,
continuation and interval rule) whose pilot is the capped multi-depth pilot,
under `experimentLaw μ ((pilotStage S J m ρ).endpoint false) q`. The
certificates are read off the paid chronological prefix
`(processHistory z.2 cap).take pilotCost` of the observed history, the prefix
the stage's own interval rule reads.

| Target | Statement |
|---|---|
| `stage_pilot_event` | (A8): for $0<\rho$, $J\ge1$, $m>0$, $\varepsilon>0$ and $m\ge8\log(2J/\varepsilon)$, with probability at least $1-\varepsilon$ both halves of (A8) hold at every depth $i+1\le J$ and the learned law dominates the gap law in distribution. |
| `stage_pilot_oracle` | (A11) on the same event: under $\rho\le1/4$ and the pilot's onset condition at depth $J$, with probability at least $1-\varepsilon$ both halves of (A8), the domination and $K_{\bar\mu,\rho}(4^J)\le2^{24}K_{\mu,\rho}(4^J)$ hold together. |
| `stage_pilot_oracle_eventually` | The same with a finite onset: some $J_0\ge1$, depending on $\mu$ and $\rho$ only and chosen before the seed type, the sign law, the stage, $m$ and $\varepsilon$, gives the event of `stage_pilot_oracle` at every $J\ge J_0$. |

Index $i<J$ stands for depth $j=i+1$. The paper's odd $m$ is not needed. (A11)
uses `zeroSelection`, the selection functional extended to laws with mass at
zero, at the budget $4^J$, with $2^{24}=16777216$. The pilot is charged its
full cap; the paper's remark that easy-law pilots stop early is not
formalized. The law is that of the stage's lower endpoint; the upper endpoint
has the same seed law and policy.

## How the proofs go

- [`Transfer.lean`](../../lean/ThresholdHC/StagePilotLaw/Transfer.lean): every
  property of the paid prefix has the same probability under the experiment of
  the stage as the same property of the pilot's word on the coins
  `Nat.pair 0 i` under the coin array, through
  `original_observable_simulation_law` and `learnedStage_pilot_history`. The
  pilot does not read the private seed, so the seed integrates out.
- [`CoinEvent.lean`](../../lean/ThresholdHC/StagePilotLaw/CoinEvent.lean): on
  the coin array, (A11) on the full event (A8), from
  `original_pilotStage_event` and `pilotStage_selection_le`.
- [`Full.lean`](../../lean/ThresholdHC/StagePilotLaw/Full.lean): the targets
  by the transfer, and the onset from `pilotOnset_eventually`.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_stage_pilot_law.py --replay --jobs 2` | 6 exact statements (the 3 targets and 3 components) and 11 transitive axiom reports over the 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [stage-pilot-law-audit.log](stage-pilot-law-audit.log) |
| `python -m unittest discover -s tools -p 'test_stage_pilot_law.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,959 constants (15,270 theorems) in 1,596 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,546 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,597 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 3
entries to `tools/definition_lock.json`, the three statements. No existing
entry changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The statements concern the pilot of an
arbitrary stage; they do not by themselves give the risk of a particular
continuation.

## Review

The item was planned by one agent and criticized by a second, which replaced
the (A11) statements by ones on the full event (A8), so that "on the same
event" holds literally, and dropped a proposed controller statement as
misleading. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them rebuilt the modules, printed
the axioms of all eight public theorems, ran the audit's scans, checked by
`rfl` that the two endpoints have the same law, and instantiated
`stage_pilot_event` on a trivial stage with $J=1$, $\varepsilon=1/2$ and
$m=24$. It found no defect in the Lean; its two minor points concerned a
docstring in the transfer module, corrected before the pin, and the
implementer's notes. These were reviews by AI agents, not a specialist referee
report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
