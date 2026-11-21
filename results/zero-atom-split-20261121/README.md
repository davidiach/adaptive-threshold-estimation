# Zero-atom split of the selection functional: library audit

The [arbitrary-law zero-quantile record](../arbitrary-law-zero-quantile-20261112/README.md)
compared the quantile design with the selection functional of a law with an
atom at zero through the identity
$K_\alpha=\min\{\rho,z+(1-z)K_{\eta,\rho/(1-z)}\}$ for
$\alpha=z\delta_0+(1-z)\eta$, and said that the identity is not Lean-checked.
Lean now checks it, in
[`lean/ThresholdHC/ZeroAtomSplit`](../../lean/ThresholdHC/ZeroAtomSplit/Full.lean).
That record is unchanged; its numerical check, the toolkit's enclosure of
$K_\eta$ and the correspondence with the toolkit's oracle split remain as it
describes them. The audit runs below were made at commit
[`703d353`](https://github.com/davidiach/adaptive-threshold-estimation/commit/703d353).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/ZeroAtomSplit/Specification.lean)
states two targets. $K_\alpha$ is the arbitrary-law selection functional
`zeroSelection`, in which a selection that charges zero has infinite entropy
and the tail weight at zero is one; $K_\eta$ is the positive-gap functional
`EntropyTail.selection`.

| Target | Statement |
|---|---|
| `zero_atom_split` | For a probability law $\eta$ of gaps in $(0,1/2]$, $0\le z<1$, $\rho>0$ and $B>0$: $K_{z\delta_0+(1-z)\eta,\rho}(B)=\min\{\rho,z+(1-z)K_{\eta,\rho/(1-z)}(B)\}$. |
| `zero_atom_split_law` | For every probability law $\alpha$ on $[0,1/2]$ with $\alpha\{0\}<1$, the same with $z=\alpha\{0\}$ and $\eta$ the normalized positive part of $\alpha$. |

The positive part is evaluated at the rarity $\rho/(1-z)$ of the identity, not
at the design rarity $(\rho-z)/(1-z)$ of the quantile design. The record states
the identity without hypotheses. The hypothesis $B>0$ is needed: in Lean
$1/\sqrt B=0$ for $B\le0$, and then the left side is zero while the right side
is $\min\{\rho,z\}$. For $\rho\le0$ both sides vanish. The identity holds for
every $\rho>0$, wider than the range $\rho\le1/4$ of the record. The law
$\alpha=\delta_0$ is outside the second target; the zero floor of the
arbitrary-law group covers it.

## How the proofs go

The proofs are in [`Support.lean`](../../lean/ThresholdHC/ZeroAtomSplit/Support.lean).

- A selection that charges zero has infinite objective (`zeroObjective_eq_top`).
  A selection that does not charge zero lies below the positive part
  (`le_of_le_zeroAtom_add`), and adding the atom adds $z$ to its objective,
  through the tail weight one at zero (`zeroObjective_add_zeroAtom`). So
  $K_{z\delta_0+\nu,\rho}=\min\{\rho,z+K_{\nu,\rho}\}$ for every finite $\nu$
  (`zeroSelection_add_zeroAtom`).
- Scaling a gap law by $c>0$ scales each objective by $c$ and divides the
  rarity by $c$, since $\sqrt{\rho c\Gamma}=c\sqrt{(\rho/c)\Gamma}$
  (`selection_smul`). With $c=1-z$ this gives the identity.
- The law form follows from the decomposition of $\alpha$ into its zero atom
  and normalized positive part, already in the arbitrary-law group.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_zero_atom_split.py --replay --jobs 3` | 5 exact statements (the 2 targets and 3 components) and 11 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [zero-atom-split-audit.log](zero-atom-split-audit.log) |
| `python -m unittest discover -s tools -p 'test_zero_atom_split.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,098 constants (13,731 theorems) in 1,469 modules, same axioms. 147 exported instances. 3,227 locked definition fingerprints. | [project-audit.log](../stopped-time-uniform-20261121/project-audit.log) of the stopped time-uniform record, the same run |
| `python tools/verify_lean_sources.py` | 1,470 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added seven
entries to `tools/definition_lock.json`: the three statements of
`StoppedTimeUniform`, the statement of `LatentThreshold`, the two statements of
`ZeroAtomSplit` and the statement of `CapIdentificationEstimate`. No existing
entry changed. The run recorded here is a later one without that flag; it
covers all four groups.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The identity concerns the selection functional
only; it says nothing about the quantile design or the toolkit's
floating-point enclosure.

## Review

Before the specification was pinned, a reviewer that had not written the proof
checked that `zeroSelection` is the zero-atom extension of the selection
functional that the record links, that the rarity is the record's
$\rho/(1-z)$, and the role of each hypothesis under Lean's conventions; it
instantiated the target at a point mass. It found no blocking problem; its
wording fixes were applied. This was a review by an AI agent, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
