# Critical quadratic law: specialist review packet

[Read the PDF](review.pdf) · [Standalone TeX](main.tex) · [Editable brief](overview.tex)

The first four pages state the claim, define and evaluate Psi, identify the vulnerable proof steps,
and distinguish paper arguments from Lean results. Pages 5–18 contain the
complete existing critical-law argument, including its three proof inputs.
This is a review package, not a record of external specialist approval.

The mathematical source is the four-file
[locked critical bundle](../../research/2026-10-27-nonlinear-critical/)
at commit `b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`.
The [source audit](../../docs/CRITICAL_AUDIT.md) records the follow-up review
and formalization boundary. Both critical minimax bounds and the actual Psi
formula, rate and universal matching-Psi counterexample are now Lean-checked.
The formal upper uses RMS coefficient 100000 and an alternative observable
construction. The formal counterexample budget is `L*(1+log L)/rho`; the
preserved paper's `rho^(-2)` sequence remains a paper derivation.

The verification table is pinned to
`eabf274cb42d4bff4daab6b58568ad6169e7f0a7`. It includes the single-coin base cost,
one common hard pair, unrestricted population transfer, separate endpoint
termination, both critical minimax rates, and the exact Psi counterexample.
It also records the completed original distribution-blind RMS upper theorem.
The mathematical proof bundle itself
remains the original four-file source identified above.

## Reproduce the packet

From the repository root:

```sh
python tools/build_critical_review.py --check
# After editing overview.tex, regenerate the standalone source:
python tools/build_critical_review.py
# Compile with Tectonic 0.17.0 into an existing output directory:
tectonic paper/critical-review/main.tex --outdir .runtime/review-pdf --keep-logs --untrusted
```

The assembler checks the original SHA-256 source lock before expanding the
proof inputs. It changes the title, date, authorship/provenance line, and layout;
source paths and hashes receive line-breaking markup. The inherited status
paragraph is replaced with the current verification boundary; shared references
are appended from `paper/gap-entropy-references.tex`. The inherited mathematical
content is preserved. Edit the brief, not the generated `main.tex` or the
locked originals. CI checks that the generated source matches its inputs;
CI does not compile or mathematically certify this PDF.

The checked-in PDF was compiled on Windows with Tectonic 0.17.0 on 28 October
2026. It has 18 A4 pages. All pages were rendered and checked as contact
sheets, with the new comparison and verification pages inspected at readable resolution.
The final TeX log has no overfull/underfull boxes or unresolved references.
Exact PDF bytes may differ with another TeX bundle or platform.

The short brief credits the project lead and AI assistance; the inherited
proof retains its original source and prior-work attribution. Its statements
and correctness remain open to the review questions on page 3.
