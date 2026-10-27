# Critical quadratic law: specialist review packet

[Read the PDF](review.pdf) · [Standalone TeX](main.tex) · [Editable brief](overview.tex)

The first three pages state the claim, identify the vulnerable proof steps,
and distinguish paper arguments from Lean results. Pages 4–16 contain the
complete existing critical-law argument, including its three proof inputs.
This is a review package, not a record of external specialist approval.

The mathematical source is the four-file
[locked critical bundle](../../research/2026-10-27-nonlinear-critical/)
at commit `b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`.
The [source audit](../../docs/CRITICAL_AUDIT.md) records the follow-up review
and formalization boundary. In particular, the full statistical critical
theorem is not Lean-checked.

The verification table includes the statistical finite-gap sign-entropy
theorem proved at `accdb144972edd255dedec50cc1cbcaa45587040`. Its continuum
restart and base-cost applications remain open. The mathematical proof bundle
itself remains the original four-file source identified above.

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
proof inputs. It changes the title, authorship/provenance line, and layout;
source paths and hashes receive line-breaking markup. It preserves the
mathematical content. Edit the brief, not the generated `main.tex` or the
locked originals. CI checks that the generated source matches its inputs;
CI does not compile or mathematically certify this PDF.

The checked-in PDF was compiled on Windows with Tectonic 0.17.0 on 27 October
2026. It has 16 A4 pages. All pages were rendered and checked as a contact
sheet, with the metadata-heavy final pages inspected at readable resolution.
The final TeX log has no overfull/underfull boxes or unresolved references.
Exact PDF bytes may differ with another TeX bundle or platform.

The short brief credits the project lead and AI assistance; the inherited
proof retains its original source and prior-work attribution. Its statements
and correctness remain open to the review questions on page 2.
