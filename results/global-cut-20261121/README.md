# Global-cut bound of the certified-selection note: library audit

The [certified-selection package](../../research/2026-10-30-certified-selection/README.md)
proves, as Corollary 6, that the best of the global upper-gap cuts, the
selection that the toolkit's `threshold_certificate` scans, has a value $V$
with $\mathcal K\le V\le Q\le\frac85\mathcal K$, and gives an exact two-atom
law on which $V\ne\mathcal K$. Lean checked the comparison
$\mathcal K\le Q\le\frac85\mathcal K$, but not the global cut. Lean now checks
the corollary and the counterexample, in
[`lean/ThresholdHC/GlobalCut`](../../lean/ThresholdHC/GlobalCut/Full.lean).
The package is unchanged. The audit runs below were made at commit
[`7b02d70`](https://github.com/davidiach/adaptive-threshold-estimation/commit/7b02d70).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/GlobalCut/Specification.lean)
defines `globalCutValue`: the selection objective minimized over the open
and closed upper cuts $\mu|_{\{d>t\}}$ and $\mu|_{\{d\ge t\}}$, $t\in\mathbb R$,
which keep the gaps above $t$ in the entropy core, capped at $\rho$ like the
selection functional $\mathcal K$. It states three targets.

| Target | Statement |
|---|---|
| `global_cut` | For every probability law of gaps, $0<\rho\le1/4$ and $B>0$: $\mathcal K\le V\le Q\le\frac85\mathcal K$, with $Q$ the closed quantile value. |
| `finite_cut` | On $n$ atoms in strictly increasing order, with any weights, $V$ is the minimum, capped at $\rho$, of the objectives of the $n+1$ selections of the $k$ largest atoms, $k=0,\ldots,n$. |
| `not_exact` | On the law with masses $9999/10000$ at $1/4$ and $1/10000$ at $1/2$, with $\rho=1/4$ and $B=10^8$: $\mathcal K<V$. |

The note defines $V$ for finite laws only. The Lean value is defined for
every law; `finite_cut` identifies it with the note's on finite laws, so the
note's corollary is `global_cut` together with `finite_cut`. The closed cuts
are needed because the quantile threshold can sit on an atom. The
correspondence with `threshold_certificate`, which sorts and merges atoms,
adds them from the largest gap and caps each candidate at $\rho$, is by
inspection; its floating-point enclosure is not checked.

## How the proofs go

The proofs are in [`Cut.lean`](../../lean/ThresholdHC/GlobalCut/Cut.lean) and
[`Full.lean`](../../lean/ThresholdHC/GlobalCut/Full.lean).

- $\mathcal K\le V$: every cut is a selection below the law.
- $V\le Q$: the quantile core is the mixture $r\,\mu|_{\{d>t\}}+(1-r)\,\mu|_{\{d\ge t\}}$
  of the open and closed cuts at the quantile threshold $t$. The cost entropy
  is superadditive and homogeneous, the square root is concave on
  $[0,\infty]$, and the remainder cost is affine in the selection, so the
  objective of the quantile core is at least the smaller of the two cut
  objectives.
- $Q\le\frac85\mathcal K$ is the existing comparison
  `locked_selection_comparison`.
- `finite_cut`: an upward-closed set of indices of increasing atoms is a top-$k$
  set.
- `not_exact`: the selection of the atom $1/4$ alone gives
  $\mathcal K\le20001/10^8$, and each of the three cuts has objective at least
  $200011/10^9$. These are hand bounds on exact expressions; $\mathcal K$ and
  $V$ are not computed exactly, and the optimality of that selection is not
  claimed.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_global_cut.py --replay --jobs 3` | 6 exact statements (the 3 targets and 3 components) and 25 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [global-cut-audit.log](global-cut-audit.log) |
| `python -m unittest discover -s tools -p 'test_global_cut.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,274 constants (13,878 theorems) in 1,483 modules, same axioms. 147 exported instances. 3,256 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,484 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added four
entries to `tools/definition_lock.json`: `globalCutValue` and the three
statements. No existing entry changed. The run recorded here is a later one
without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. Theorem 8's band-crossing counterexample and the
package's polynomial identities are not targets. The toolkit's
`threshold_certificate` itself is not verified.

## Review

Before the specification was pinned, two reviewers that had not written the
proofs read the group. One compared the definitions with the note and the
toolkit: the orientation of the cut, the top-$k$ index condition and the
counterexample's data all match, and $\mathcal K<V$ is a genuine strict
inequality between finite reals. The other checked each step of the proof of
$V\le Q$, including the infinite cases of the concavity lemma, and printed
the axioms. Neither found a blocking problem. The local notations of the
first draft were inlined, since the audit rejects notation. These were
reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
