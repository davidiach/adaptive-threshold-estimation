# Research packages and current status

For the current mathematical narrative and full proofs, start with the
[consolidated v5 manuscript](../paper/v5/paper.pdf). The packages below preserve
the detailed provenance and evidence behind its appendices.

These packages preserve the reviewed sources, failed approaches, exact source
locks, diagnostics and numerical evidence from separate research passes.
Their original reports and acceptance records describe their own checkpoints;
later results do not rewrite those historical records.

| Package | Accepted scope | Evidence |
|---|---|---|
| [Power margins above two](2026-10-27-route-a/CHECKPOINT.md) | Known-rarity power-margin rate for alpha greater than two. | Reviewed paper proof; exact finite diagnostics; separate conditional-kernel Lean bridge. |
| [Minimax audit](2026-10-27-minimax-audit/FINAL_REPORT.md) | Critical upper construction, scope audit and numerical comparison. | Reviewed paper components and explicitly limited numerical evidence. |
| [Earlier critical result](2026-10-27-critical-two/CHECKPOINT.md) | Sharp critical rate for the specified noninteractive additive class. | Reviewed paper proof; its then-open interactive converse is addressed by the later full result. |
| [Full critical result](2026-10-27-nonlinear-critical/CHECKPOINT.md) | Sharp rarity-constrained minimax rate for the fixed quadratic law, permitting interaction and nonlinear output; counterexample to the general matching-Psi upper conjecture. | Reviewed paper proof, not Lean-checked or externally specialist-reviewed. |
| [Population step](2026-10-27-population-step/FINAL_REPORT.md) | Single-coin obstruction, conditional information reduction, radial counterexample and calibrated radial upper bound. | Reviewed paper proofs and exact finite experiments. The radial counterexample rules out one proposed proof route, not the later full critical theorem. |
| [Nonlinear feedback](2026-10-27-nonlinear-population/FINAL_REPORT.md) | Strict feedback advantage at a deterministic two-flip cap, bounded-depth obstruction, finite approximation framework, and a synthetic feedback experiment. | Reviewed paper proofs, exact rational certificates, and numerical evidence. No general finite minimax program or arbitrary-law sharp rate was solved. |

The full critical theorem concerns the fixed law F(d)=(4d)^2. A sharp replacement
for Psi on arbitrary magnitude laws remains open. Earlier statements that the
matching-Psi conjecture itself remained open record the state before the full
critical proof. The finite feedback advantage uses a deterministic cap and
does not claim an asymptotic rate improvement under a uniform expected budget.

Current mathematical scopes are collected in [the results guide](../docs/RESULTS.md).
The completed Tier 5/6 formal results are independent of these paper-proof labels.

From the repository root, replay the integrated identities and diagnostics with:

```sh
python tools/verify_research.py
python tools/verify_population_research.py
```

The second command checks all 200 sealed package files, runs exact arithmetic
and policy certificates in disposable copies, audits the 7,680 recorded
experiment rows, and replays the predesignated replicate in each of 240 cells.
It creates fresh evidence under the ignored `.runtime/` directory and preserves
all original checkpoints. Neither command certifies the continuum paper proofs.
