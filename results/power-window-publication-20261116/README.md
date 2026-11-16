# Publication of the complete uniform power-law bounds

The [192-page manuscript](../../paper/v6/builds/power-window-complete-20261116.pdf)
publishes the uniform power-law entropy estimate and deterministic quantile
comparison of Lemma 14.12 and Theorem 14.13, together with their unconditional
RMS and confidence consequences. The status table contains 32 Lean-checked
entries and one paper-proof entry, each in its stated scope. Corollary 14.14
and Remark 14.15 remain paper results in that separate entry.

The [proof record](../power-window-complete-20261116/README.md) checks all
five unchanged frozen targets: the Phi formula, actual core cost and entropy,
deterministic quantile comparison, RMS bounds and both confidence bounds.
Its 16 exact statements and 78 transitive axiom reports cover exponent two
and arbitrary scale. The RMS coefficients are `10^-17/sqrt(2)` and `60002`;
the confidence lower coefficient is `10^-17/sqrt(2)` and the upper coefficient
is `1500000`. The paper's `10^-18` and `66000` are weaker; its confidence
upper coefficient agrees. No unproved entropy or quantile premise remains.

The proof checkpoint is
[`6965262b95490eeabf5d5158ad55e0393027f28c`](https://github.com/davidiach/adaptive-threshold-estimation/commit/6965262b95490eeabf5d5158ad55e0393027f28c).
The TeX sources are pinned to
[`cbfd73ef3d4a5db1481f9a55ce9e1640ad3c916b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/cbfd73ef3d4a5db1481f9a55ce9e1640ad3c916b).
The [build record](../../paper/v6/builds/power-window-complete-20261116.json)
and [manuscript CI record](manuscript-ci.json) identify two successful Ubuntu
builds with byte-identical PDFs. The PDF has 192 pages, 33 embedded font
objects, 402 unique source labels and 29 resolved citations. All ten changed
pages and contents page 2 were rendered with Poppler and visually inspected.
No new clipping, overlap or displaced header/footer was found; 182 pages
retain identical extracted body text and word positions. The only TeX
warning is the inherited 5.16461 pt overfull line in Appendix C.

The [whole-project audit](project-audit.log) checks 13,276 constants,
including 10,763 theorems, across 1,240 modules, using only `propext`,
`Classical.choice` and `Quot.sound`. It also validates 125 exported instances
and all 2,402 definition fingerprints. No definition fingerprint was added
or changed. The existing native build cache was completed by the full
PowerWindow build before the whole-project audit's `--no-build` step.
The [test log](validation-tests.log) records 30 Psi/power guard tests and
42 manuscript/status-generator tests, all passing.

The [source identity manifest](proof-source-manifest.json) connects the
manuscript and validation checkpoints: every listed Lean source, verifier
and build input is identical. The [base PR record](base-pr117-ci.json)
identifies the merged #117 head and all its passing checks. That evidence
does not establish CI success for a later follow-up head. The new proof
verification here is local; the two manuscript builds identify their own
source commit. Issue #100 awaits the follow-up PR's integration and
actual-head CI, with no remaining unproved frozen power-window target.

[Reconciliation](reconciliation.json) records these boundaries.
[SHA256SUMS](SHA256SUMS) identifies the record, build logs and PDF.
All earlier proof/publication records, frozen specifications and the
floating-point numerical script retain their original bytes.
