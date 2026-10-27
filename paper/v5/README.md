# Consolidated version 5

[Read the manuscript](paper.pdf) · [Open the LaTeX project](main.tex)

This is the current combined research draft: the original minimax law and
unbiased characterization, the 713 construction, rare-event power regimes,
and the critical quadratic result correcting the matching-Psi conjecture.
The main statements are in sections 2, 7 and 11. Section 12 gives the exact
formal verification boundary. Appendices A–C contain the longer rare-event
proofs, including their published external inputs.

The full critical theorem and original distribution-blind upper bound remain
paper proofs. The statistical finite-gap sign-entropy ingredient is proved
in Lean. The manuscript has no independent external specialist review, and
the new consolidation itself has not had a separate agent review.
For a narrower critical-result review, use the
[three-page brief and full-proof packet](../critical-review/review.pdf).

## Source and editorial scope

The original v4 and research packages remain unchanged. [sources.json](sources.json)
records their identities after line-ending normalization, the starting commit,
and the formal checkpoint linked from the manuscript.
[build_v5.py](../../tools/build_v5.py) generates six inherited-source files,
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
  theorem's hidden-magnitude model is distinguished from the stronger
  revealed/selected-magnitude paper statements.
- Repeated diagnostics and priority commentary remain in the source archives.
  Mathematical proof dependencies are retained, with an explicit Sion citation.

The editable exposition is in `frontmatter.tex`, `constant713.tex`,
`rare-events.tex`, and `verification.tex`; `main.tex` controls the layout.
Do not edit the six generated files directly.

## Reproduce

From the repository root:

```sh
python tools/build_v5.py
python tools/build_v5.py --check
tectonic paper/v5/main.tex --outdir /path/to/disposable-output --keep-logs --untrusted
```

The project also compiles in the desktop LaTeX editor. The published PDF was
exported with Tectonic 0.17.0, rendered with Poppler, and visually inspected.
It has 55 pages, no unresolved references or overfull boxes. The source check
resolves 141 unique labels and 19 bibliography citations. Typesetting and source
identity checks do not constitute a new mathematical proof or independent review.
