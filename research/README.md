# Research packages and current status

For the current mathematical narrative and full proofs, start with the
[consolidated v6 manuscript](../paper/v6/README.md). It combines the
[v5 manuscript](../paper/v5/README.md) with the
[general-law rare-event manuscript](../paper/rare-event/README.md), which keeps
the 29 October entropy-tail characterization's audit records, and the
[finite-gap rare-event manuscript](../paper/finite-gap-rare-events/README.md).
The packages below preserve the detailed provenance and evidence behind its
appendices. Sections 14 and 18 of v6 now include the certified-selection
comparison and finite-law suffix theorem. Appendix R gives the hard-budget
RMS reduction and applications. Appendix S carries the statistical transfer of
the confidence package, §14.8 the closed form of $\Psi$, and Appendix AA the
sharp RMS constant. Each row below says what its package proved at its own
checkpoint and what has been checked in Lean since.

These packages preserve the reviewed sources, failed approaches, exact source
locks, diagnostics and numerical evidence from separate research passes.
Their original reports and acceptance records describe their own checkpoints;
later results do not rewrite those historical records.

| Package | Accepted scope | Evidence |
|---|---|---|
| [How loose is the upper constant 512?](2026-11-18-upper-constant/README.md) | For the distribution-blind algorithm behind the upper constant, the worst RMS-to-modulus ratio found is about 7.6, and a proof along the paper's route with sharp per-gap constants would give about 9; the proven constant is 512. | Exact floating-point risk formula over finite grids of gaps, sign laws and budgets, cross-checked by simulation of the toolkit implementation. Numerical evidence only; no proof and no Lean check. Lean has since checked smaller constants for the same algorithm; the [results guide](../docs/RESULTS.md#minimax-law-and-unbiasedness) states the current one. |
| [Two updates at stopping times](2026-11-18-two-stopping-updates/README.md) | Even two schedule replacements triggered by observed answers give worst-case RMS at least 0.186764460. | Exact rational optimization and Lean proof of strict separation from the fully adaptive witness. |
| [One update at a stopping time](2026-11-18-stopping-update/README.md) | A single schedule replacement triggered by observed follow-up answers has worst-case RMS at least 0.186844275. | Exact rational stopping calculation and Lean comparison with the fully adaptive policy in the population experiment. |
| [One scheduled update after the pilot](2026-11-18-scheduled-update/README.md) | With a pilot-chosen split and a second batch chosen from ordered first-batch answers, worst RMS is at least 0.186960371. | Lean population-risk lower bound and strict comparison against the adaptive witness, with an independent integer calculation. |
| [Feedback after the 18-flip pilot](2026-11-18-pilot-feedback/README.md) | At gap 1/5, every policy committing to its seven distinct-label follow-ups after the pilot has worst RMS at least 0.18735887. The adaptive policy attains less than 0.186752. | Exact rational Bayes calculation and Lean proofs of ordered-transcript reconstruction and the strict comparison in the original randomized experiment. |
| [RMS constants, oracle efficiency and stopping caps](2026-11-17-rms-constants/README.md) | The sharp unrestricted RMS lower coefficient is $1/6$ in the ordinary model and both magnitude oracles. For $B\ge25$ the best coefficient lies in $[0.175198,\,0.186752]$; its exact value is open. Also gives sharp oracle asymptotics and a smaller sufficient cap for the optimized stopping programs. | In the audited library and checked in CI: the constant $1/6$, its optimality, equality at $B=4$, $\sqrt{59/2100}$ for $B\ge25$, both oracles ([SharpRMS](../lean/ThresholdHC/SharpRMS/Full.lean)) and the cap comparison ([SquareRootCap](../lean/ThresholdHC/SquareRootCap/Full.lean)); see the [audit record](../results/sharp-rms-20261117/README.md). The paper proves $1/6$ in Appendix AA. Since 18 November 2026 also in the audited library and CI: the bracket for $B\ge25$ ([LargeBudgetRMS](../lean/ThresholdHC/LargeBudgetRMS/Full.lean), [audit record](../results/large-budget-rms-20261118/README.md)), stated in Appendix AA as Theorem AA.7. Paper proofs with exact-arithmetic checks: the oracle asymptotics and the $3\sqrt7/2$ bound for the infinite stopping program. |
| [$\Psi$ in closed form and the critical window](2026-11-09-psi-closed-form/README.md) | $\Psi$ equals the entropy-free quantile form within a factor $\sqrt2$; $\Psi\le\mathcal K$, which derives the $\Psi$ lower bound from the entropy-tail law; the distance of $\Psi$ from the rate; power-margin rates with constants independent of the exponent. | Paper proofs in v6 §14.8, resting on Corollary 14.6 and Theorem S.6. Floating-point check of every inequality and constant. Not Lean-checked at this checkpoint. Since then Lean checks $\Psi\le\mathcal K$ ([PsiSelection](../lean/ThresholdHC/PsiSelection/Full.lean)) and Proposition 14.9, Theorem 14.11, Lemma 14.12 and Theorem 14.13 ([PsiClosedForm](../lean/ThresholdHC/PsiClosedForm/Full.lean), [PsiGap](../lean/ThresholdHC/PsiGap/Full.lean), [PsiSharpness](../lean/ThresholdHC/PsiSharpness/Full.lean), [PowerWindow](../lean/ThresholdHC/PowerWindow/Full.lean)). Corollary 14.14 and Remark 14.15 remain paper proofs. |
| [Prescribed-accuracy finite-law selection](2026-11-06-selection-approximation/README.md) | A fully polynomial `(1+epsilon)` approximation to the capped entropy-tail functional, with an actual suffix witness and no repeated-cost assumption. Exact efficient selection remains open. | Paper proof and rational prototype with exhaustive subset comparisons. Entropy perturbation and certified-bin state compression are Lean-checked. The assembled approximation theorem is since Lean-checked as well ([note](../docs/FINITE_SELECTION_APPROXIMATION.md)); the polynomial bit-complexity argument and Python execution are not. No independent review. |
| [General-law rare-event manuscript v2](../paper/rare-event/README.md) | Arbitrary known-law entropy-tail characterization, stopping dual, and qualified genie certificates. | Audited paper proof with exact finite certificates. Both entropy-tail halves, the two-sided law, the stopping dual, factor-sixteen certificate, cap identification and genie results have since been [Lean-checked](../docs/RESULTS.md#general-law-rare-event-characterization), including the paper's explicit lower coefficient $10^{-17}$ for the entropy-tail risk. Existing manuscripts and historical audit identities are preserved. |
| [Certified selection](2026-10-30-certified-selection/README.md) | Quantile-to-selection factor 8/5 (1 + 2 sqrt 2 in finite-gap revision 2, 5/3 in the [computation note](../docs/RARE_EVENT_COMPUTATION.md)), bandwise-suffix exact finite selection, total-variation and band-preserving rounding stability of the selection functional, and an exact-rational evaluator in the toolkit. A [later result](../docs/OPTIMAL_QUANTILE_FACTOR.md), since Lean-checked ([QuantileOptimality](../lean/ThresholdHC/QuantileOptimality/Full.lean)), identifies the sharp factor as a unique scalar root. | Lean checks the [full comparison](../results/quantile-selection-20261104/README.md), its [sharpening to $31/20$](../results/quantile-price-20261104/README.md) and [finite-law suffix theorem](../results/bandwise-suffix-20261104/README.md). Lean also checks [stability, rounding and finite approximation](../results/selection-stability-20261104/README.md). Exact rational certificates from unverified Python. An integration review adds the 1.4604 obstruction and a separately written high-precision cross-check. |
| [Hard-budget RMS](2026-10-30-hard-budget-rms/README.md) | Independent geometric-fallback reduction from expected work to a pathwise observation cap at factor sqrt(32) in RMS; hard-cap corollaries for the distribution-blind RMS law, the critical quadratic law and the known general-law entropy-tail rate; an observation-capping driver in the toolkit. | The [Lean audit](../results/hard-budget-rms-20261104/README.md) proves the observable reduction and all three hard-cap applications. The new general-law upper coefficient is $160000$. Exact finite recurrence and schedule audits and timeout counterexamples. Scoped extraction from a delivered archive that is not in the repository. |
| [Confidence transfer](2026-10-30-confidence-transfer/README.md) | Smoothed Hellinger-to-KL transfer giving high-confidence rates at budget B/log(1/delta) for the general law and the critical law, under expected or hard budgets; capped independent-block median amplification; nested intervals with error spending, valid under data-dependent stopping; two toolkit drivers. | Lean checks the [two-sided quarter-smoothing inequality](../results/quarter-smoothing-20261104/README.md). Lean checks the [single-type adaptive transfer and common-pair lower bound](../results/confidence-population-20261104/README.md). The [critical confidence lower bound](../results/critical-confidence-20261104/README.md) is verified in Lean. The adaptive-type extension is now [Lean-checked through unbounded stopping](../results/adaptive-types-20261105/README.md), and so is the capped median, in the [fixed-confidence audit](../results/known-law-confidence-20261104/README.md). The [unknown-law confidence sequence and lower bound](../docs/UNKNOWN_LAW_CONFIDENCE.md) are later paper results. Exact finite smoothing, factorization and path-counting audits. AI integration review, no specialist review. Scoped extraction from delivered archives that are not in the repository. |
| [Power margins above two](2026-10-27-route-a/CHECKPOINT.md) | Known-rarity power-margin rate for alpha greater than two. | Reviewed paper proof; exact finite diagnostics; separate conditional-kernel Lean bridge. The rate itself is later proved in Lean by a different construction, [RareAboveTwo/Full.lean](../lean/ThresholdHC/RareAboveTwo/Full.lean). |
| [Minimax audit](2026-10-27-minimax-audit/FINAL_REPORT.md) | Critical upper construction, scope audit and numerical comparison. | Reviewed paper components and explicitly limited numerical evidence. The critical upper theorem is later proved in Lean, [CriticalUpper/Full.lean](../lean/ThresholdHC/CriticalUpper/Full.lean). |
| [Earlier critical result](2026-10-27-critical-two/CHECKPOINT.md) | Sharp critical rate for the specified noninteractive additive class. | Reviewed paper proof; its then-open interactive converse is addressed by the later full result. |
| [Full critical result](2026-10-27-nonlinear-critical/CHECKPOINT.md) | Sharp rarity-constrained minimax rate for the fixed quadratic law, permitting interaction and nonlinear output; counterexample to the general matching-Psi upper conjecture. | Reviewed paper proof, not externally specialist-reviewed. Both minimax bounds and a matching-Psi counterexample were later proved in Lean; see [the results guide](../docs/RESULTS.md#critical-power-margin-full-minimax-characterization). |
| [Population step](2026-10-27-population-step/FINAL_REPORT.md) | Single-coin obstruction, conditional information reduction, radial counterexample and calibrated radial upper bound. | Reviewed paper proofs and exact finite experiments. The radial counterexample rules out one proposed proof route, not the later full critical theorem. |
| [Nonlinear feedback](2026-10-27-nonlinear-population/FINAL_REPORT.md) | Strict feedback advantage at a deterministic two-flip cap, bounded-depth obstruction, finite approximation framework, and a synthetic feedback experiment. | Reviewed paper proofs, exact rational certificates, and numerical evidence. No general finite minimax program or arbitrary-law sharp rate was solved. |

The full critical theorem concerns the fixed law F(d)=(4d)^2. The later
[general-law manuscript](../paper/rare-event/README.md) supplies an entropy-tail
replacement for Psi as an audited paper proof; both directions are now Lean-checked
with conservative universal constants. Earlier statements that the
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
The certified-selection package has its own
[replay commands](2026-10-30-certified-selection/README.md#replay), which also
write to `.runtime/` and compare with its tracked evidence. The hard-budget RMS
package's [exact audit](2026-10-30-hard-budget-rms/README.md#reproduction)
writes only to `.runtime/hard-budget-rms/`; it has no tracked evidence records.
The confidence-transfer package's
[audits](2026-10-30-confidence-transfer/README.md#reproduce-from-the-repository-root)
write only to `.runtime/confidence-transfer/` and likewise have none.

Five recent packages are replayed from their own guides and are not
part of the two commands above or of CI:
[selection approximation](2026-11-06-selection-approximation/README.md#verification-performed),
[$\Psi$ in closed form](2026-11-09-psi-closed-form/README.md#numerical-check),
[RMS constants](2026-11-17-rms-constants/README.md#reproducing-the-formal-checks),
[pilot feedback](2026-11-18-pilot-feedback/README.md#verification-scope-and-replay) and
[the upper-constant study](2026-11-18-upper-constant/README.md#reproduce).
For the [scheduled-update package](2026-11-18-scheduled-update/README.md#replay),
`python tools/verify_population_research.py` checks the proof-source hashes
and reruns the independent integer calculation; its Lean replay is in its
guide.
Three checkers of the RMS-constants package import SymPy, which
`requirements.txt` does not list.
