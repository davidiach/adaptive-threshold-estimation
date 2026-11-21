# The 20+5 revisit witness: library audit

The rms-constants package
([`research/2026-11-17-rms-constants`](../../research/2026-11-17-rms-constants/README.md),
section *The coefficient for budgets of at least 25*) describes a rule with a
20-flip pilot at the gap $1/5$ under a hard cap of 25 flips. Flip 20
distinct coins and let $j$ be the number of heads. For $5\le j\le9$ revisit
five distinct coins that showed heads, for $11\le j\le15$ five that showed
tails, and otherwise flip five fresh coins. The estimate depends on $j$ and
on the head count among the final five flips, and Lean proves its RMS risk
at most $0.188087$ in research-only files. The
[large-budget record](../large-budget-rms-20261118/README.md) promoted the
sharper pilot witness $0.186752$ and lists these five files as not
promoted. They are now in the audited library, in
[`lean/ThresholdHC/RevisitUpper`](../../lean/ThresholdHC/RevisitUpper/Full.lean).
The research package and the published large-budget record are unchanged.
The audit runs below were made at commit
[`95e9a3b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/95e9a3b).

## Statement

[`Specification.lean`](../../lean/ThresholdHC/RevisitUpper/Specification.lean)
states the labelling rule as a property `RevisitRule L` of an arbitrary
reader $L$ of the answer list: pilot flip $n<20$ uses the new label $n$; after
a pilot word with $5\le j\le9$ heads each follow-up label is a pilot coin that
showed heads, with $11\le j\le15$ one that showed tails, and otherwise the new
label $20+k$; follow-up labels are distinct. The single target is

| Target | Statement |
|---|---|
| `revisit_witness` | Some deterministic estimator runs a reader obeying `RevisitRule`, stopped at 25 flips, with output a function of the pilot head count and the follow-up head count. It makes at most 25 flips on every path, meets the budget $25$ under every gap law, and has maximal RMS risk at most $0.188087$ at the point mass $\delta_{1/5}$. |

The increasing order in which the source picks the revisited coins is not
stated; the rule requires only distinct pilot coins of the right outcome. The
rational estimate table appears only as an existential function. The
conditional-binomial law of the revisits is the component `history_step`.
The minimax and coefficient corollaries at $0.188087$ are components; the
audited `LargeBudgetRMS` targets at $0.186752$ are sharper and stay the
library's bound.

## The copies

The five research files were copied with their namespace renamed from
`ThresholdHC.SharpRMS.Revisit` to `ThresholdHC.RevisitUpper`, their imports
pointed at the library, the file-level options `maxRecDepth` and
`maxHeartbeats` scoped to the two declarations that need them, and the final
carriage return stripped. No proof line changed. The library constants they
use stay in `ThresholdHC.SharpRMS.Revisit`. Two new modules,
[`LabelRule.lean`](../../lean/ThresholdHC/RevisitUpper/LabelRule.lean) and
[`Full.lean`](../../lean/ThresholdHC/RevisitUpper/Full.lean), prove that the
library reader obeys the rule and assemble the target.

SHA-256 digests of each research file and its library copy:

```text
RevisitHistory
  research 7391c0272f34db6ca727a7f1d3e3d504b4bbe6c6af2d091729fd1969bc979303
  library  66ec076b26e09696f4c51ad6b114b98a3c6657a30983344100f3b1b7d171c76e
RevisitCertificate
  research 304194af7b769c7b38aca41b6b9efbba31b144374f7c327158a04e42909161c1
  library  843ec4073bb0216747f8ab945f135f61d29b3ccd573fc7acfab836432d72842e
RevisitExperiment
  research 722461a3ae27119a722a6014a705877ff03f042fdf8e21170300616f87584049
  library  52c106858d3dc710ea7421b2d3db621905827f3c154acd077122750cca4b03fe
RevisitRisk
  research a4762299083e930b817cb32550cd24d621f58af231a37db041d821e548ab544d
  library  c0df38329a4371c31008f7f1c7b9ddfcbc35a113850646ed509f76673b576dd4
RevisitWitness
  research 2de3185e430f95ece0fe9905e553898fb4962805fa074a09de380d0597a19bc7
  library  3657ee45f1b2364d3b126e6b9f7438e473e83f5a9162450604c653d21cea5469
```

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_revisit_upper.py --replay --jobs 3` | 5 exact statements (the target and 4 components) and 23 transitive axiom reports over the 8 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 8 modules replayed through the independent kernel checker, including the `decide +kernel` risk certificate. | [revisit-upper-audit.log](revisit-upper-audit.log) |
| `python -m unittest discover -s tools -p 'test_revisit_upper.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,105 constants (14,570 theorems) in 1,543 modules, same axioms. 150 exported instances; 6 registered orphans, unchanged. 3,394 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,544 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 24
entries to `tools/definition_lock.json`: the rule and the statement, the
estimator, its policy and table, the certificate polynomials, and their
private helpers. No existing entry changed. The run recorded here is a later
one without that flag.

## Scope

These audits check that the stated type is proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The witness adds no new bound: the coefficient
bracket for $B\ge25$ stays $[0.175198,\,0.186752]$. The research package and
the large-budget record describe their own checkpoints and are unchanged.

## Review

The item was planned by one agent, criticized by a second, which reduced it
to one target with the labelling rule as a property of an arbitrary reader,
and written by a third. Before the specification was pinned, a fourth agent
that had not written the proofs rebuilt all eight modules with warnings as
errors and got byte-identical compiled files, replayed every module through
the kernel checker (the certificate in 12 seconds), confirmed by `Iff.rfl`
that the statement unfolds to the source claim written from the base
definitions, compared the copies with the research files, and probed
non-vacuity: the library reader satisfies the rule, an always-fresh reader
fails it, and the checked lower bound $0.175198$ rules out a trivial witness.
It found no defects. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
