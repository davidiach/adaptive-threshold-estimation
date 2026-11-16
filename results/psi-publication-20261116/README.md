# Publication of the sharp Psi results and power-law foundation

The [192-page manuscript](../../paper/v6/builds/psi-sharpness-20261116.pdf)
separates the checked sharp closed form and entropy gap of Psi from the
uniform-power results that still have paper proofs. The status table now
has 31 Lean-checked entries and one paper-proof entry, each in its stated scope.

The new [sharpness audit](../psi-sharpness-20261116/README.md) completes the
two-atom equality and the entropy bound by the number of occupied bands.
The [power-law foundation](../power-window-foundation-20261116/README.md)
identifies the actual quantile split and inverse-square core cost, including
exponent two and arbitrary scale. It also checks that the deterministic
uniform quantile comparison implies the full RMS and both confidence bounds,
retaining that unproved comparison as an explicit premise.

The remaining formal work in issue #100 is the uniform band-cost entropy
estimate and the deterministic quantile comparison. Corollary 14.14 and
Remark 14.15 remain paper results outside the current formal targets.
The numerical script and all earlier proof and publication records are unchanged.

The TeX sources are pinned to
[`70e1638c00d7a38f7775acb68c45f0a09b98cbdb`](https://github.com/davidiach/adaptive-threshold-estimation/commit/70e1638c00d7a38f7775acb68c45f0a09b98cbdb).
The [build record](../../paper/v6/builds/psi-sharpness-20261116.json) and
[manuscript CI record](manuscript-ci.json) identify two successful Ubuntu
builds with byte-identical PDFs. The PDF has 192 pages, 33 embedded font
objects, 402 unique source labels and 29 resolved citations. All 32 changed
pages and contents page 2 were rendered with Poppler and visually inspected.
No new clipping, overlap or displaced header/footer was found; 160 pages
retain identical extracted body text and word positions. The only TeX warning
is the inherited 5.16461 pt overfull line in Appendix C.

The two new local audits verify 13 exact statements and 42 transitive axiom
reports using only `propext`, `Classical.choice` and `Quot.sound`.
Their 12 guard tests, the full set of 24 Psi guard tests and the 42 manuscript
and status-generator tests pass. The [whole-project audit](project-audit.log)
checks all project constants and definition fingerprints. Windows command
length required building modules in batches before the same audit's
`--no-build --add-definitions` step. Its definition lock adds exactly fifteen
new entries and changes no existing fingerprint.

The [source identity manifest](proof-source-manifest.json) connects the
manuscript checkpoint to the validation checkpoint: every listed Lean source,
verifier and build input is identical. The definition lock separately adds
the fifteen new definitions. The [base PR record](base-pr116-ci.json) records
all fifteen passing checks and the merge of #116; it is evidence for that
base head, not CI evidence for the new proofs. Consult the review PR's actual
head for its CI result. No later-head CI success is inferred from an earlier run.

[Reconciliation](reconciliation.json) records the remaining proof boundary.
[SHA256SUMS](SHA256SUMS) identifies this record, its build logs and the PDF.
