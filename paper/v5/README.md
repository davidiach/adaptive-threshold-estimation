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
critical minimax lower bound is also proved in Lean, including the common pair,
population transfer and endpoint termination. The matching critical upper and
explicit Psi comparison remain paper proofs, as do the confidence characterization
and unbiased converse. Formal links are pinned to
`236eb2d4f286f8987f74f293c129258f517f2ec4`.
The manuscript has no independent external specialist review, and
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
  theorems' hidden-magnitude model is distinguished from the stronger
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
python -m unittest discover -s tools -p 'test_build_v5.py' -v
tectonic paper/v5/main.tex --outdir /path/to/disposable-output --keep-logs --untrusted
```

The project also compiles in the desktop LaTeX editor. The published PDF was
exported with Tectonic 0.17.0 on 28 October 2026, rendered with Poppler,
and visually inspected.
It has 56 pages, no unresolved references or overfull boxes. The source check
resolves 141 unique labels and 20 bibliography citations, and rejects uncited
references. The PDF predates the citation of Chen--Li--Qiao in Appendix C,
which replaced an inline arXiv reference; re-export to pick up that line. Typesetting and source
identity checks do not constitute a new mathematical proof or independent review.

The assembly regression checks preserve function arguments such as `q(D)`,
`R(B)` and `mu(E)` when prefixing equation tags. The earlier global parenthesis
replacement altered those expressions in Appendix C; this version restores
the original formulas. The inherited proof sources were unaffected.
