# Tier5 current-source replay and semantic boundary

This is new verification of the working tree at HEAD `a8a8dc49115aabdd1fba8d53d3390eb0a5eee864`, not a claim that all proof helpers were committed at that SHA. The Tier5 helpers were untracked concurrent work. They were read and built without modifying their sources or the historical results.

`replay_tier5.py` imports the unchanged `tools/verify_tier5.py` functions. It checks the exact original lock closure and all preceding locks, scans all Tier5 declarations using the existing validator, checks that all nine specified targets are actually present, builds the nineteen Tier5 source modules, and writes a separate exact-type/axiom audit into this directory. It hashes the complete local import closure before and after. No validators, allowed axioms, specifications, or lock manifests were changed.

Observed result in `tier5_replay.json`:

- `valid=true`, `complete=true`; nine exact target types; 109/109 root axiom reports.
- Axiom union: `Classical.choice`, `Quot.sound`, `propext` only.
- All 44 local dependency sources and original locks unchanged during replay.
- Historical `results/tier5_status.json` hashes matched the inspected source bytes, and that historical file was left unchanged.
- Cache-aware build: 9.56 seconds. Fresh elaboration of the exact-type/axiom audit: 18.02 seconds. Build output reports 18,255 jobs, which includes cached dependency work and must not be described as 18,255 fresh kernel rebuilds.
- Toolchain file: `leanprover/lean4:v4.36.0-rc1`; local lake executable and `ELAN_HOME` are pinned explicitly by the script. Reproduction command: `python research/2026-10-27-population-step/audit/replay_tier5.py`.

The kernel-checked named targets are:

| Declaration in `ThresholdHC.Tier5` | Fixed statement type |
| --- | --- |
| `creation_law_total` | `CreationTotalStatement` |
| `creation_law_consistent` | `CreationConsistencyStatement` |
| `creation_finite_kl_bound` | `CreationFiniteKLStatement` |
| `creation_stops` | `CreationStopsStatement` |
| `creation_kl_eq_iSup` | `CreationKLSupremumStatement` |
| `creation_infinite_kl_bound` | `CreationInfiniteKLStatement` |
| `creation_observable_kl_bound` | `CreationObservableKLStatement` |
| `unbounded_creation_example` | `UnboundedCreationExampleStatement` |
| `tier5_landmark` | `Tier5LandmarkStatement` |

The finite cylinder model uses labels in Nat, permits first use, revisits, and interleaving without a deterministic number-of-coins cap. A finite decision tree induces a finite cap for defining each cylinder; that construction does not impose one global cap on the policy. The full-transcript KL bound follows from the supplied realized prefix laws and finite plus-law expected work; minus-law nontermination is permitted. Measurable observations of the augmented seed/tape inherit the information bound. These are meaningful later-tier results beyond a scalar inequality or a fixed finite collection.

Their assumptions remain essential. The two realized experiments are inputs to `RealizesCreationPrefixes`; the theorem does not universally construct an iid reservoir experiment for each arbitrary magnitude law and policy. The environment may be carried in an augmented seed, and the policy is permitted to depend on that seed. A hidden-environment population experiment needs its own faithful realization and observation map. The formal pair has sign probabilities `1/2 +/- eta`, with `0<=eta<=1/8`, gap in `(0,1/2]`, and `gap*eta<=h/8`. Thus the formal priors lie in `[3/8,5/8]`, not the user's global rare-event class with rho<=1/4.

The existential example is nonvacuous but specific: it uses gap 1/2, priors 5/8 and 3/8, and a seed-selected unbounded number of new labels with finite expected work. It does not discharge general iid-reservoir existence. The replay therefore establishes completion of these nine exact Tier5 statements, not a Lean proof of arbitrary-law rare-event minimax, the critical single-coin obstruction, its small-bias extension, or the candidate Psi functional's statistical attainability. The separate single-coin paper proof does not depend on Tier5.

## Portable source snapshots

All 44 audited local dependency sources are preserved byte-for-byte under `tier5-sources/<repository-relative-path>`, with hashes in `tier5_snapshot_manifest.json` matching `tier5_replay.json`. These are attributed snapshots of existing concurrent Tier5 work and its older dependencies, not new proofs authored in this audit. Capture checked the source before copying, the snapshot after copying, and the source again. No original file changed. The subsequently executed default check reported 44 verified snapshots, zero missing original sources, and zero overwritten files.

On a clean checkout, the restore helper checks every snapshot and every existing destination before any writes. Existing conflicting files cause failure; only missing files can be created, with exclusive creation and a final hash check. It never overwrites existing files, locks, historical results, or git metadata:

```powershell
python research/2026-10-27-population-step/audit/restore_tier5_sources.py --restore
```

With the repository's documented Lean toolchain available, run from `lean/`:

```powershell
lake build ThresholdHC.Tier5.Full
lake env lean ../research/2026-10-27-population-step/audit/CurrentTier5Audit.lean
```

The `Full` import closure was separately checked to include all nineteen Tier5 modules. These minimal reproduction commands need only the committed baseline and the new snapshots, not the historical untracked `results/tier5_status.json`. The richer original `replay_tier5.py` additionally compares that historical record and therefore expects it to be present. No additional Lean build was performed while packaging the snapshots.
