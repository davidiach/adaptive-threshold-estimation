# Consolidated version 5

[Read the manuscript](paper.pdf) · [Open the LaTeX project](main.tex)

This is the current combined research draft: the original minimax law and
unbiased characterization, the 713 construction, rare-event power regimes,
and the critical quadratic result correcting the matching-Psi conjecture.
The main statements are in sections 2, 7 and 11. Section 12 gives the exact
formal verification boundary. Appendices A–C contain the longer rare-event
proofs, including their published external inputs.

The original RMS law is Lean-checked in both directions, with lower coefficient
1/64 and upper coefficient 512 and one distribution-blind algorithm. The full
critical minimax law is also proved in Lean in both directions, including the
common pair, population transfer, endpoint termination and observable upper
construction with coefficient 100000. The exact Psi formula, rate and failure
of every universal matching-Psi upper are formalized. The formal counterexample
uses budget `L*(1+log L)/rho`; the paper's `rho^(-2)` sequence remains a paper
derivation. The unbiased converse now proves inverse-gap integrability and
the `I²/16` variance-work lower bound for all uniformly unbiased observable
adaptive estimators. Its [proof](../../lean/ThresholdHC/UnbiasedConverse/Full.lean)
and [audit](../../results/unbiased_converse_001.json) are linked at
`631886e16ddff5b8e93b73860bf6552b956128be`. The 713 upper construction retains
its conditional-kernel scope. The confidence characterization and other
rare-event regimes retain paper-proof status. Earlier formal links are pinned to
`eabf274cb42d4bff4daab6b58568ad6169e7f0a7`; the additive all-size proof links
use `ebd36676693b66814bc2a379529499428ab98650`.
The manuscript has received AI review, but has no independent external
specialist review.
For a narrower critical-result review, use the
[four-page brief and full-proof packet](../critical-review/review.pdf).

The shared addendum on pages 26–27 extends finite-gap entropy to every
gap count with coefficient 1/4096 and gives explicit single-coin base-cost
coefficients `1/10000000000` (raw moment) and `1/15000000000` (variance).
The original coefficient 1/512 remains valid for `log K >= 32`.
Its [current audit](../../results/critical_all_sizes_002.json) is separate from the
original critical-law audit; no explicit population minimax constant is claimed.

## Source and editorial scope

The original v4 and research packages remain unchanged. [sources.json](sources.json)
records their identities after line-ending normalization, the starting commit,
and the formal checkpoints linked from the manuscript.
[build_v5.py](../../tools/build_v5.py) generates six inherited-source files
and a local copy of the shared addendum,
prefixes appendix labels and explicit equation tags, resolves their references,
and shares a single bibliography. Its editorial changes are explicit:

- Theorem 2 now uses 713, with a full additional proof of the separate 23 and
  31 bounds. The original finite-budget classifier still uses its original
  threshold and constants.
- The false matching-Psi conjecture is replaced by the critical correction.
  Historical open-problem wording is updated where later results settle it.
- Original proofs retain their assumptions. The rare-event global constraint
  is not replaced by a pointwise constraint, and the fixed quadratic theorem
  is not extended to all exponents or scales.
- Current formal status appears next to the main results. The core Lean
  theorems' hidden-magnitude model is distinguished from the stronger
  revealed/selected-magnitude paper statements.
- Repeated diagnostics and priority commentary remain in the source archives.
  Mathematical proof dependencies are retained, with an explicit Sion citation.

The editable exposition is in `frontmatter.tex`, `constant713.tex`,
`rare-events.tex`, and `verification.tex`; `main.tex` controls the layout.
Edit the shared addendum in [../finite-gap-extension.tex](../finite-gap-extension.tex)
and regenerate its local copy. Do not edit the seven generated files directly.
The generated folder is self-contained for compilation or upload to a TeX editor.
The source check follows the actual inputs from `main.tex`, rejecting missing,
external, repeated, or omitted project files before checking labels and citations.

## Reproduce

From the repository root:

```sh
python tools/build_v5.py
python tools/build_v5.py --check
python -m unittest discover -s tools -p 'test_build_v5.py' -v
tectonic paper/v5/main.tex --outdir /path/to/disposable-output --keep-logs --untrusted
```

The project also compiles in the desktop LaTeX editor. The published PDF was
exported with Tectonic 0.17.0 on 28 October 2026, rendered with Poppler,
and visually inspected.
It has 59 pages, no unresolved references or overfull boxes. The source check
resolves 141 unique labels and 24 bibliography citations, and rejects uncited
references. The PDF includes the corrected Chen--Li--Qiao citation in Appendix C.
Typesetting and source
identity checks do not constitute a new mathematical proof or independent review.

The assembly regression checks preserve function arguments such as `q(D)`,
`R(B)` and `mu(E)` when prefixing equation tags. The earlier global parenthesis
replacement altered those expressions in Appendix C; this version restores
the original formulas. The inherited proof sources were unaffected.
