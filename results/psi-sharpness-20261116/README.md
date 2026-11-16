# Sharpness of Psi and occupied-band entropy

This record completes the sharpness claims of v6 Proposition 14.9 and the
occupied-band part of Theorem 14.11. It supplements the preserved
[closed-form](../psi-closed-form-20261116/README.md) and
[entropy-gap](../psi-gap-20261116/README.md) records.

For every probability gap law and `0 < rho <= 1/4`, the actual quantile
core has a finite, positive number `n` of bands with nonzero inverse-square
cost. Its normalized cost entropy satisfies `E <= log n <= log log_2(1/t)`.
For the two-atom law with masses `rho` and `1-rho`, gaps satisfying
`d2 = d1 sqrt((1-rho)/rho)`, and `h <= d1/2`, the proof gives
`Psi = sqrt(2) h rho/d1` and `Q0 = 2 h rho/d1 = sqrt(2) Psi`.
The concrete case `rho=1/5`, `d1=1/8`, `d2=1/4`, `B=1024` proves that
the assumptions are nonvacuous. The other sharpness regime, `h >= t`,
was already checked in `PsiClosedForm`.

The [specification](../../lean/ThresholdHC/PsiSharpness/Specification.lean)
was committed at `144e75d` before the proofs. The
[proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/a5edeef11ce9ca2737acf4b11f9dd871e80135ee)
contains the completed proofs and audit. The [exact audit input](audit.lean)
and [report](audit.log) check five statements and every one of the fifteen
declarations in the directory. The only transitive axioms are `propext`,
`Classical.choice` and `Quot.sound`. [Source hashes and scope](status.json)
identify this local audit; they are not a claim of CI success on a later head.

Run `python tools/verify_psi_sharpness.py` with the pinned Lean toolchain.
Its six regression tests cover changed specifications, missing targets,
hidden or omitted modules, proof escapes, unsupported declaration forms
and missing or unsound axiom reports. CI runs both the audit and tests.
No existing specification, definition fingerprint or historical record was changed.

The [power-law foundation](../power-window-foundation-20261116/README.md)
is a separate result. The uniform-power entropy and statistical bounds
remain formal work in issue #100.
