# Published verification evidence

These files record particular source checkpoints and experiments. Use
[docs/RESULTS.md](../docs/RESULTS.md) for current claim scope and
[docs/VERIFY.md](../docs/VERIFY.md) to reproduce a check. A stored pass applies to
the sources and targets it audited; it does not establish that a later checkout
or CI run passes. A record's source hashes describe its own checkpoint, so they
can differ from the current files after a later proof-only change: the
[hard-budget record](hard-budget-rms-20261104/README.md), for example, lists
eight Lean files that were refactored afterwards without changing a
statement. For the current tree the evidence is the CI run on that commit.

The folder holds 148 dated record directories, named for a result and a
date, and the loose JSON and log files of the first phases of the project.
The table below indexes the records that the guides cite. Later sections
describe the remaining records in prose: the time-uniform bounds, cost
grouping, cap truncation and the unknown-law adaptation proof. A record
that a later one extends says so in its row or paragraph; the later record
is the current evidence for that result.

## Records referenced by the current guides

| Claim or check | Published record |
|---|---|
| Selection and three-piece forms of the entropy-tail law: (61) $=$ (62) before and after the cap, the law with $0<c<C$, hard measurable partitions and a hard minimizer on finite laws: library statement, axiom and kernel-replay audits | [entropy-tail-forms-20261121](entropy-tail-forms-20261121/README.md) |
| Noninterval optimal assignment of the rare-event discussion: the eight table enclosures, the unique hard minimum $\{1/2,1/8\}$, the inactive cap and no optimal interval retention: library statement, axiom and kernel-replay audits | [noninterval-selection-20261121](noninterval-selection-20261121/README.md) |
| Global-cut bound of the certified-selection note (Corollary 6): $\mathcal K\le V\le Q\le\frac85\mathcal K$, $V$ is the scan of the $n+1$ top-$k$ cuts on finite laws, and $\mathcal K<V$ on the note's two-atom law: library statement, axiom and kernel-replay audits | [global-cut-20261121](global-cut-20261121/README.md) |
| Magnitude-oracle upper bound $R\le\omega_\mu(B^{-1/2})/2$ for both oracles, its floor form, and the coefficient $1/2$ as exactly the best: library statement, axiom and kernel-replay audits | [oracle-upper-20261121](oracle-upper-20261121/README.md) |
| Sharpness of the magnitude-oracle upper coefficient $1/2$: point masses at small gaps have both oracle risks above $c\,\omega(B^{-1/2})$ for every $c<1/2$; the upper bound is not stated: library statement, axiom and kernel-replay audits | [oracle-sharpness-20261121](oracle-sharpness-20261121/README.md) |
| Strictness of the sharp RMS bound: for every gap law and every $B\ge1$ other than four, $R_\mu(B)>\omega_\mu(B^{-1/2})/6$, also under both oracles, so equality forces $B=4$: library statement, axiom and kernel-replay audits | [sharp-strict-20261121](sharp-strict-20261121/README.md) |
| RMS coefficient exactly $1/6$ for budgets through four (and both oracles there), for protocols with at most three flips per coin, and conditionally for any class containing the four-fresh-flip protocols: library statement, axiom and kernel-replay audits | [restricted-rms-20261121](restricted-rms-20261121/README.md) |
| Residual steps of the confidence-transfer note: $r^{\rm exp}\ge\Psi(\sqrt{\log(1/\delta)/B})/8192$ for every gap law, and the exact-power-law confidence rate above two under both budget conventions: library statement, axiom and kernel-replay audits | [confidence-transfer-steps-20261121](confidence-transfer-steps-20261121/README.md) |
| Proposition `prop:psi-null`, $\mathfrak J_0(b)\ge(\Psi(h)-4b)_+^2/(192h^2)$ for every gap law, and its corollary $R\ge\Psi(B^{-1/2})/8192$: library statement, axiom and kernel-replay audits | [psi-null-20261121](psi-null-20261121/README.md) |
| Bias subtraction in Proposition `prop:psi-null`: for every $c<4$ and $K>0$, the bound with $cb$ and $K$ in place of $4b$ and $192$ fails on the remark's two-atom laws: library statement, axiom and kernel-replay audits | [bias-subtraction-20261121](bias-subtraction-20261121/README.md) |
| Common-pair RMS bound at the critical law, $R\ge\min\{\rho/32,\sqrt{a\rho L(1+\log L)/B}\}/128$ for some $a>0$: library statement, axiom and kernel-replay audits | [critical-pair-rms-20261121](critical-pair-rms-20261121/README.md) |
| Clipping boundary: the bounded-kurtosis transfer to the clipped risk, its uniform corollary, and the seed-noise counterexample, also in the original experiment: library statement, axiom and kernel-replay audits | [clipping-boundary-20261121](clipping-boundary-20261121/README.md) |
| Fixed-plan majority bound: expected work $n(2k+1)$, bias at most $e_m$, variance at most $1/(4n)$, RMS at most $\sqrt{e_m^2+1/(4n)}$, and $e_m$ in closed form for uniform rates: library statement, axiom and kernel-replay audits | [fixed-plan-20261121](fixed-plan-20261121/README.md) |
| Stopping-program factor $3\sqrt7/2$: $R\le P_\infty\le(3\sqrt7/2)R$, $R\le P_N\le3\sqrt7\,R<8R$ for $N\ge4B/9$, and the genie test: library statement, axiom and kernel-replay audits | [program-factor-20261121](program-factor-20261121/README.md) |
| Explicit fixed-cap estimate $\Delta_N/2\ge\rho\|h\|_2^2/(4\|h\|_\infty)$ after the fixed-cap identification theorem, with $h=1-\operatorname{proj}_{\mathcal V_L}1$: library statement, axiom and kernel-replay audits | [cap-identification-estimate-20261121](cap-identification-estimate-20261121/README.md) |
| Zero-atom split $K_\alpha=\min\{\rho,z+(1-z)K_{\eta,\rho/(1-z)}\}$ for $\alpha=z\delta_0+(1-z)\eta$, the identity the zero-quantile record used without a Lean proof: library statement, axiom and kernel-replay audits | [zero-atom-split-20261121](zero-atom-split-20261121/README.md) |
| Threshold form of the target: $\theta=G_{\mu,q}(P>1/2)$ for every gap law and sign law, not only laws with a density: library statement, axiom and kernel-replay audits | [latent-threshold-20261121](latent-threshold-20261121/README.md) |
| Time-uniform remark: stopping at budget $n$ gives a fixed-budget interval, so every estimate from the seed and the first $n$ observations obeys the coefficient $10^{-17}$, and display (TU1) with $10^{-22}$ holds at every $n\ge2$ with $\log\log n\le(10^{10}-1)\log(1/\delta)$: library statement, axiom and kernel-replay audits | [stopped-time-uniform-20261121](stopped-time-uniform-20261121/README.md) |
| Corollaries `cor:one-gap` and `cor:mse` (both displays) of the finite-gap manuscript: the one-gap rate with the entropy–tail constants $10^{-17}$ and $28000$, and the mean-square forms with $c_0^2=10^{-40}$ and $2C_0^2=2\cdot30001^2$: library statement, axiom and kernel-replay audits | [finite-gap-corollaries-20261121](finite-gap-corollaries-20261121/README.md) |
| Proposition `prop:bounded`, first sentence: no almost surely nonnegative unbiased output when $\mu((0,1/2))>0$: library statement, axiom and kernel-replay audits | [nonnegative-unbiased-20261121](nonnegative-unbiased-20261121/README.md) |
| Explicit constants that frozen statements leave existential or prove only per algorithm: the hidden-model confidence coefficient $15/(256\sqrt2)$, the rare-event lower coefficient $1/256$ and the single-coin second moment $28\rho$: library statement, axiom and kernel-replay audits | [explicit-constants-20261121](explicit-constants-20261121/README.md) |
| Pilot-feedback separations at gap $1/5$ with budget $25$ (precommitted follow-ups at least $0.18735887$, one scheduled update at least $0.186960371$, both above the adaptive witness), promoted from two research packages: library statement, axiom and kernel-replay audits | [pilot-feedback-20261120](pilot-feedback-20261120/README.md) |
| Fifteen targets, twelve of them paper and guide claims with only a written proof, a numerical check or an existential constant: the critical theorem with explicit constants and the $\Psi$ sequence in its model, the sharp unbiased coefficient $1/16$ at every fixed gap, the known point-mass constant $1/2$, the 713 second moment, $c_*>1.462554551279$ and selection stability with $20Q/31$: library statement, axiom and kernel-replay audits | [paper-statements-20261120](paper-statements-20261120/README.md) |
| RMS constants $1/6$ and $12$ under a stochastic envelope, $1/6$ under a pathwise cap, and the paper's divergence sequence for $\Psi$ at the quadratic law: library statement, axiom and kernel-replay audits | [paper-corollaries-20261120](paper-corollaries-20261120/README.md) |
| Corollary 14.14 and Remark 14.15 of v6 (the critical window $3/2\le\alpha\le3$ and the regimes away from and near exponent two), the last tracked results with a paper proof only: library statement, axiom and kernel-replay audits | [critical-window-20261120](critical-window-20261120/README.md) |
| Typeset release v6 manuscript with the review corrections of 19 November (§14.8, Appendix AB; no change of content): build logs, page comparison and its script, toolchain check | [release-publication-20261119](release-publication-20261119/README.md) |
| Typeset v6 manuscript with the RMS upper constant $12$ (Theorem AB.1, Appendix AB rewritten): build logs, page comparison and toolchain check | [upper-constant-12-publication-20261119](upper-constant-12-publication-20261119/README.md) |
| Typeset v6 manuscript with the RMS upper constant $15$ (Theorem AB.1, Appendix AB): build logs, page comparison and toolchain check | [upper-constant-publication-20261119](upper-constant-publication-20261119/README.md) |
| Pilot events (A8) and (A11) of the paid learning stage under the law of the whole stage, with (A11) on the same event: library statement, axiom and kernel-replay audits | [stage-pilot-law-20261121](stage-pilot-law-20261121/README.md) |
| A fee per created coin changes the cost by at most the factor $1+c$, for every adaptive estimator, with the charged minimax sandwich and rate: library statement, axiom and kernel-replay audits | [creation-charge-20261121](creation-charge-20261121/README.md) |
| Clipping the output to $[0,1]$ can only help: budget kept, RMS risk not raised, the same minimax risk over $[0,1]$-valued estimators, and a $[0,1]$-valued family with constant $12$: library statement, axiom and kernel-replay audits | [clipped-output-20261121](clipped-output-20261121/README.md) |
| RMS upper constant $12$, from the padded call cost $26/5$ and one budget level calibrated at the scale $B/4$ in place of the mixture below: library statement, axiom and kernel-replay audits | [upper-scale-20261119](upper-scale-20261119/README.md) |
| RMS upper constant $13$ for the mixture below, from the exact vote-change probability, at most one quarter, the stage that `upper-sign-20261119` extends: library statement, axiom and kernel-replay audits | [upper-quarter-20261119](upper-quarter-20261119/README.md) |
| RMS upper constant $15$ for the mixture below, from the sign-change bound on the disagreement below the cap scale: library statement, axiom and kernel-replay audits | [upper-sign-20261119](upper-sign-20261119/README.md) |
| RMS upper constant $17$ for the mixture below, from a sharper call second moment, the stage that `upper-sign-20261119` extends: library statement, axiom and kernel-replay audits | [upper-disagreement-20261119](upper-disagreement-20261119/README.md) |
| RMS upper constant $19$ for the mixture below, from a sharper padded call cost, the stage that `upper-disagreement-20261119` extends: library statement, axiom and kernel-replay audits | [upper-cost-20261118](upper-cost-20261118/README.md) |
| RMS upper constant $27$ for a distribution-blind mixture of two budget levels of the algorithm below, which uses the whole budget, the stage that `upper-cost-20261118` extends: library statement, axiom and kernel-replay audits | [upper-mixture-20261118](upper-mixture-20261118/README.md) |
| RMS upper constant $36$ for the distribution-blind algorithm, from a sharper call second moment, the stage that `upper-mixture-20261118` extends: library statement, axiom and kernel-replay audits | [upper-moment-20261118](upper-moment-20261118/README.md) |
| RMS upper constant $45$ for the same algorithm, from a sharper per-level work bound, the stage that `upper-moment-20261118` extends: library statement, axiom and kernel-replay audits | [upper-work-20261118](upper-work-20261118/README.md) |
| RMS upper constant $119$ for the same algorithm, the earlier stage that `upper-work-20261118` extends: library statement, axiom and kernel-replay audits | [upper-constant-20261118](upper-constant-20261118/README.md) |
| The 20+5 revisit witness with RMS at most $0.188087$ at the gap $1/5$ under a hard cap of 25 flips, moved from the rms-constants package: library statement, axiom and kernel-replay audits | [revisit-upper-20261121](revisit-upper-20261121/README.md) |
| RMS lower coefficient for $B\ge25$ in $[0.175198,0.186752]$: library statement, axiom and kernel-replay audits | [large-budget-rms-20261118](large-budget-rms-20261118/README.md) |
| Typeset v6 manuscript with the large-budget bracket (Theorem AA.7) and the $4B/9$ cap (Theorem Q.1): build logs, page comparison and toolchain check | [large-budget-publication-20261118](large-budget-publication-20261118/README.md) |
| Sharp RMS lower constant $1/6$ in all three models and the square-root cap comparison: library statement, axiom and kernel-replay audits | [sharp-rms-20261117](sharp-rms-20261117/README.md) |
| Typeset v6 manuscript with the sharp RMS constant and Appendix AA: build logs, page comparison and toolchain check | [sharp-rms-constant-publication-20261118](sharp-rms-constant-publication-20261118/README.md) |
| Typeset v6 manuscript with the review corrections: build logs, page comparison and toolchain check | [review-corrections-publication-20261117](review-corrections-publication-20261117/README.md) |
| Zero-residual envelope, rounding and conditional transfer certificates (#85) | [envelope-transfer-certificates-20261117](envelope-transfer-certificates-20261117/README.md) |
| Bounded global menu/DP/approximation output certificates (#85) | [global-selection-certificates-20261117](global-selection-certificates-20261117/README.md) |
| Finite-law measure, feasible-objective and oracle output certificates (#85) | [finite-law-certificates-20261117](finite-law-certificates-20261117/README.md) |
| Deterministic sqrt/log/entropy output certificates and checker soundness (#85) | [deterministic-certificates-20261117](deterministic-certificates-20261117/README.md) |
| Finite-law relative approximation, original-K endpoints and `Q*S` extensions (#93) | [finite-selection-approximation-20261117](finite-selection-approximation-20261117/README.md) |
| Secondary-claim inventory and explicit paper-only dispositions (#89) | [secondary-claims-20261116](secondary-claims-20261116/README.md) |
| Complete uniform power-law manuscript and evidence reconciliation | [power-window-publication-20261116](power-window-publication-20261116/README.md) |
| Sharp Psi results, power-law foundation and manuscript scope reconciliation | [psi-publication-20261116](psi-publication-20261116/README.md) |
| Completed arbitrary-law manuscript, status and proof-evidence reconciliation | [adaptation-publication-20261116](adaptation-publication-20261116/README.md) |
| Entropy perturbation and certified-bin state-compression invariant | [selection-approximation-20261106](selection-approximation-20261106/README.md) |
| Original frozen Lean target audit | [lean_checkpoint.json](lean_checkpoint.json), [lean_score.json](lean_score.json) |
| Uniform713 and information milestones | [uniform713_status.json](uniform713_status.json), [tier3_status.json](tier3_status.json), [tier4_status.json](tier4_status.json), [tier5_status.json](tier5_status.json) |
| Main RMS lower bound, original frozen target with constant $1/64$ (the sharp $1/6$ is in the first row) | [tier6_status.json](tier6_status.json) |
| Distribution-blind RMS upper bound | [blind_upper_components_002.json](blind_upper_components_002.json) |
| Full critical quadratic lower bound | [critical_components_016.json](critical_components_016.json) |
| Full critical quadratic upper bound | [critical_upper_components_003.json](critical_upper_components_003.json) |
| Critical Psi formula and minimax separation | [critical_psi_001.json](critical_psi_001.json) |
| All-size entropy and explicit single-coin costs | [critical_all_sizes_002.json](critical_all_sizes_002.json) |
| Observable unbiased converse | [unbiased_converse_001.json](unbiased_converse_001.json) |
| Observable 713 and unbiased existence characterization | [observable713_001.json](observable713_001.json) |
| Confidence characterization | [confidence_001.json](confidence_001.json) |
| Magnitude-oracle lower bounds | [oracle_lower_001.json](oracle_lower_001.json) |
| Observable rare-event rate above alpha two | [rare_above_two_001.json](rare_above_two_001.json) |
| Rare-event upper bounds, quantile comparison, stopping program, identification and genie certificates (full rebuild; see the note below) | [rare-event-full-20261031](rare-event-full-20261031/README.md) |
| Complete entropy-tail lower and two-sided law (cached dependencies; source and artifact hashes recorded) | [entropy-tail-complete-20261101](entropy-tail-complete-20261101/README.md) |
| Explicit arbitrary-law entropy-tail and quantile lower bounds | [entropy-tail-explicit-20261104](entropy-tail-explicit-20261104/README.md) |
| Arbitrary-law $\Psi$ lower bound through the entropy-tail law | [psi-selection-20261109](psi-selection-20261109/README.md) |
| Closed form of $\Psi$ within a factor $\sqrt2$ | [psi-closed-form-20261116](psi-closed-form-20261116/README.md) |
| Distance of $\Psi$ from the rate, through the entropy of the quantile core | [psi-gap-20261116](psi-gap-20261116/README.md) |
| Two-atom sharpness and occupied-band entropy | [psi-sharpness-20261116](psi-sharpness-20261116/README.md) |
| Uniform power-law entropy, quantile and statistical bounds | [power-window-complete-20261116](power-window-complete-20261116/README.md) |
| Power-law quantile split and inverse-square core cost | [power-window-foundation-20261116](power-window-foundation-20261116/README.md) |
| Whole-project build, axiom audit and main-theorem kernel replay | [project-axioms-20261109](project-axioms-20261109/README.md) |
| Whole-project audit with the exported-instance checks and the definition lock | [project-definitions-20261114](project-definitions-20261114/README.md) |
| Finite-law bandwise-suffix optimizer and sufficient search family | [bandwise-suffix-20261104](bandwise-suffix-20261104/README.md) |
| Total variation, rounding, transported enclosures and finite approximation | [selection-stability-20261104](selection-stability-20261104/README.md) |
| Quarter smoothing in both KL directions | [quarter-smoothing-20261104](quarter-smoothing-20261104/README.md) |
| Generic RMS obstruction transfer and additive submeasure localization with coefficient $1/128$, conditional on a single-coin obstruction premise that Lean established for no gap law until [psi-null-20261121](psi-null-20261121/README.md) | [rms-localization-20261105](rms-localization-20261105/README.md) |
| General-law confidence coefficients $10^{-17}$ and $750000$ | [entropy-confidence-20261105](entropy-confidence-20261105/README.md) |
| Fractional-submeasure additive confidence localization with coefficient $1/128$, from the same obstruction premise | [additive-confidence-20261105](additive-confidence-20261105/README.md) |
| Common pairs from variance–null-work obstructions and the $1/128$ confidence consequence, given such an obstruction | [common-pair-20261105](common-pair-20261105/README.md) |
| Countable-reservoir termination counterexample: finite work under one law does not transfer termination, for every realization of the creation model: library statement, axiom and kernel-replay audits | [reservoir-termination-20261121](reservoir-termination-20261121/README.md) |
| Selected-type information transfer through unbounded stopping | [adaptive-types-20261105](adaptive-types-20261105/README.md) |
| Fresh-state upper-bound transfer and complete observed-state rates | [observed-state-upper-20261105](observed-state-upper-20261105/README.md) |
| The nested-simulation class of `cor:nested` and transcriptions of the Giles–Haji-Ali Assumptions 2.1 and 2.4, with uniform constants: library statement, axiom and kernel-replay audits | [nested-assumptions-20261121](nested-assumptions-20261121/README.md) |
| Continuous-magnitude observed-state lower bounds and regularity | [continuous-observed-lower-20261105](continuous-observed-lower-20261105/README.md) |
| The Hoeffding replication count $M=\lceil32\Delta^{-2}\log(2/\delta)\rceil$ of the finite-cell observed-state bound: library statement, axiom and kernel-replay audits | [observed-hoeffding-20261121](observed-hoeffding-20261121/README.md) |
| Finite-cell observed-state lower bound | [finite-observed-20261105](finite-observed-20261105/README.md) |
| Smooth-density complexity and unbiased impossibility | [smooth-density-20261105](smooth-density-20261105/README.md) |
| Prior-family and per-flip information inequalities for the all-law time-uniform lower bound (the complete theorem is checked separately in [anytime-asymptotic-20261105](anytime-asymptotic-20261105/README.md)) | [anytime-lower-20261105](anytime-lower-20261105/README.md) |
| Common prior families and information bounds for the time-uniform lower bounds: 11 exact statements. The earlier checkpoint of the record above | [anytime-lower-family-20261105](anytime-lower-family-20261105/README.md) |
| Repeated inspection of a fixed-time interval: coverage $3/4$ at every fixed $n$, failure $0.42809100970105\ldots>1/4$ when checked up to 512: library statement, axiom and kernel-replay audits | [repeated-check-20261121](repeated-check-20261121/README.md) |
| Observable time-uniform confidence for known laws | [anytime-confidence-20261105](anytime-confidence-20261105/README.md) |
| Logarithmic and intermediate rare power margins | [shifted-power-20261105](shifted-power-20261105/README.md) |
| Rare power margins below exponent one | [sublinear-power-20261105](sublinear-power-20261105/README.md) |
| Unknown laws under a stochastic envelope | [stochastic-envelope-20261105](stochastic-envelope-20261105/README.md) |
| Fixed confidence at the effective budget for every known law | [known-law-confidence-20261104](known-law-confidence-20261104/README.md) |
| Hard-budget fallback and three RMS minimax bounds | [hard-budget-rms-20261104](hard-budget-rms-20261104/README.md) |
| Critical-law minimax confidence lower bound | [critical-confidence-20261104](critical-confidence-20261104/README.md) |
| Uniform finite-cap convergence and the linear sufficient cap | [genie-rate-20261104](genie-rate-20261104/README.md) |
| Upper end $c_*<1.462554551280$ of the sharp quantile factor and the whole of `thm:sharp-quantile-factor`, by a kernel-checked bisection cover: library statement, axiom and kernel-replay audits | [quantile-factor-upper-20261121](quantile-factor-upper-20261121/README.md) |
| Exact scalar-root quantile factor and finite-law sharpness | [quantile-optimality-20261105](quantile-optimality-20261105/README.md) |
| The finite laws that realize sharpness of the quantile factor: 50 exact statements. A component of the record above | [finite-law-family-20261105](finite-law-family-20261105/README.md) |
| All-law quantile upper comparison at the exact scalar-root factor | [sharp-quantile-upper-20261105](sharp-quantile-upper-20261105/README.md) |
| Sharp finite-core selection reduction and entropy Lipschitz bound | [quantile-core-reduction-20261105](quantile-core-reduction-20261105/README.md) |
| The 1-Lipschitz square-root cost entropy and skipped-tail absorption: 17 exact statements. A component of the record above | [quantile-lipschitz-20261105](quantile-lipschitz-20261105/README.md) |
| Sharp finite-vector quantile factor and unique scalar root | [optimal-quantile-root-20261105](optimal-quantile-root-20261105/README.md) |
| The finite-vector characterization of the quantile factor: 13 exact statements. An earlier component of the record above | [optimal-quantile-finite-20261105](optimal-quantile-finite-20261105/README.md) |
| Equivalence of the quantile factor with the infinite partition-series inequality: 29 exact statements. An earlier component of the record above | [optimal-quantile-series-20261105](optimal-quantile-series-20261105/README.md) |
| General-law $31/20$ quantile comparison | [quantile-price-20261104](quantile-price-20261104/README.md) |
| Single-type population confidence transfer and common-pair lower bound | [confidence-population-20261104](confidence-population-20261104/README.md) |
| Eight-fifths quantile-selection comparison for arbitrary laws | [quantile-selection-20261104](quantile-selection-20261104/README.md) |
| Direct finite-law quantile bounds and estimator quantifiers | [direct-finite-quantile-20261104](direct-finite-quantile-20261104/README.md) |
| Universal closed-quantile minimax corollary (cached dependencies) | [closed-quantile-law-20261101](closed-quantile-law-20261101/README.md) |
| Constant search and scope | [constants_theory.json](constants_theory.json), [constants_finite_grid.json](constants_finite_grid.json), [process account](../docs/process/TRACK_B.md) |
| Real-valued benchmark | [real_comparison.json](real_comparison.json), [real_verification.json](real_verification.json), [benchmark protocol](../benchmark/README.md) |

The `rare-event-full-20261031` record was produced by a parallel integration
of #33, on branch `feat/rare-event-verified-integration-20261030` (commit
`fc099bb`), and is imported here unchanged. It certifies that branch's proof
commit `2036bd1`: a rebuild of all 518 local dependency modules and an
exact-type and transitive-axiom audit of 1,789 declarations. Of the 263
modules imported from #33, 262 are byte-identical in `main`. The other,
`Genie/AtomConicModel.lean`, differs only by a removed trailing space. The
record audited that branch's own bridge to the frozen interface
(`EntropyTailBridge/`), not `main`'s
[`EntropyTail/Bridge.lean`](../lean/ThresholdHC/EntropyTail/Bridge.lean) and
[`Upper.lean`](../lean/ThresholdHC/EntropyTail/Upper.lean). `main`'s bridge is
checked by `verify_entropy_tail.py` in the `entropy-tail-upper` CI job. The
record's reproduction tool, `tools/verify_rare_event_completion.py`, exists
only on that branch.

Rare-event manuscript evidence lives beside that publication, in its
[build record](../paper/rare-event/v2/VERIFICATION.json) and
[audit index](../paper/rare-event/audit/README.md). The finite-gap manuscript
keeps its file hashes and check scope in its own
[SHA256SUMS](../paper/finite-gap-rare-events/SHA256SUMS) and
[provenance note](../paper/finite-gap-rare-events/PROVENANCE.md). Sealed research checkpoints
remain with their [research packages](../research/README.md).

## Interpret a record

Check its source identity, target list, scope, and completion fields together.
Numbered records preserve successive audits; a higher number is not a stronger
theorem by itself. For example, a critical lower-only audit can retain
`full_critical_minimax_theorem_verified=false` while a separate upper audit
completes the characterization. Read the
[critical audit explanation](../docs/CRITICAL_AUDIT.md#current-formal-boundary).

Files containing `baseline`, `attempt`, `draft`, `foundations`, or earlier
checkpoint numbers preserve the development history. Logs record build and
diagnostic details; numerical tables support only the experiments they describe.
Do not infer universal mathematical claims from a numerical score or infer
current CI status from a historical log.

## Fresh runs and publication

Several baseline and tier verifiers overwrite tracked files here. Run those in
a disposable checkout containing the change being checked. The later theorem
audits that save logs write them under `.runtime/`. Most audits added from
4 November onward only print their kernel report; the selection-approximation
and output-certificate audits write a fresh directory under `.runtime/`. The [tool index](../tools/README.md) describes the
other temporary output locations. Keep local reruns out of the published records.

When a task calls for publishing new evidence, add a separately identified
record with its source identity, commands, outcome, and precise scope. Preserve
the prior records and update this index and the current claim guide as needed.
Never rename, overwrite, or rehash a historical artifact to make it describe
newer work.

The [observable sequential-testing audit](anytime-sequential-20261105/README.md) checks eight exact statements, including first-crossing summability and infinitely many width violations in the original adaptive experiment.

The [infinite-moment tail-family audit](anytime-tail-20261105/README.md) checks fifteen exact statements through the adaptive observable information transfer and an explicit unbounded integer-budget schedule.

The [complete time-uniform lower-bound audit](anytime-asymptotic-20261105/README.md) checks fourteen exact statements, including the all-law asymptotic comparison and observable interval consequence with coefficient $10^{-22}$.

## Finite-menu cost grouping

The [native 14-statement audit](band-cost-formal-20261105/README.md) verifies
the mathematical compression algorithm, state bounds, entropy price,
exact saving comparison and interval certificates. The
[new 13-statement connection](gap-law-menus-20261105/README.md) additionally
constructs the actual finite-law menus and proves their compressed optimum
equals the original $K$, including atomic cost and saving formulas.
Python execution remains unverified. The
[64-band example audit](band-cost-example-20261121/README.md) of
21 November 2026 checks the guide's example for the formal solver: the
optimizer, its strict uniqueness among hard masks, and 4,160 transitions and
65 terminal states.

## Ordinary cap truncation

The [native ten-statement audit](finite-cap-truncation-20261105/README.md)
verifies a uniform square-root rate for the ordinary optimized cap program,
its output-preserving certificate construction, and the explicit risk bound.
Optimality and the corresponding genie rate remain open.

The [finite-family adaptation component audit](law-adaptation-20261105/README.md)
checks 17 exact types, including observable parity, bounded-average concentration,
identification, selected-event transfer and the delayed oracle-rate comparison.
The [22-statement realization audit](law-adaptation-realization-20261105/README.md)
adds moment determinacy and the complete observable finite-family controller,
with actual flip accounting, nested compatible intervals and joint all-budget
coverage and oracle width. At that checkpoint arbitrary-law adaptation had a
[paper proof](../docs/ARBITRARY_LAW_ADAPTATION.md) only; the
[full controller record](arbitrary-law-controller-20261116/README.md) below now
checks the complete theorem.

The [finite arbitrary-law entropy transport audit](arbitrary-law-entropy-20261106/README.md)
adds 15 exact statements, including the geometric factor-three comparison.
It does not yet establish the full arbitrary-law adaptation theorem.

The [finite CDF-envelope audit](arbitrary-law-envelope-20261106/README.md)
adds 25 exact statements and 24 axiom reports for the conservative finite
measure, its zero atom and CDF domination from finite grid bounds.

The [observable learned-law stage audit](arbitrary-law-stage-20261106/README.md)
adds 17 exact statements and 16 axiom reports: a valid learned probability
law on every word, fresh continuation labels, physical caps, history readback,
and the original-experiment joint endpoint law. Statistical instantiation
and the full all-budget controller remain outside this component.

The [countable entropy-transport audit](arbitrary-law-countable-20261106/README.md)
adds 16 exact statements and axiom reports. It extends the factor-three bound
to countably many locally summable destination columns, allows infinite total
cost and entropy, and identifies the result with canonical Gamma for finite
gap measures with a supplied band-cell decomposition.

The [increasing-gap coupling and selection audit](arbitrary-law-coupling-20261106/README.md)
adds 32 exact statements and transitive reports. It constructs canonical
band cells from a finite increasing coupling on positive gaps, lifts every
fractional selection, preserves mass and domination, and proves the original
selection comparison with coefficient sqrt(3), allowing infinite moments
and entropy. CDF coupling existence and the zero-atom extension remain separate
at that checkpoint.

The [CDF coupling and zero-atom audit](arbitrary-law-zero-cdf-20261106/README.md)
adds 47 exact statements and transitive reports. It constructs the common-
uniform increasing coupling from CDF domination, extends the entropy-tail
functional to unresolved mass at zero, proves exact agreement with positive-
gap K, and derives the sqrt(3) comparison from CDF domination on `[0,1/2]`.

The [dominated-mass audit](arbitrary-law-dominated-20261106/README.md)
adds 22 exact statements and transitive reports for bounded density
restriction, entropy and tail algebra, residual control, and comparison (A5)
for finite measures, allowing infinite entropy and preserving the cap.

The [concrete light-contraction audit](arbitrary-law-light-20261106/README.md)
adds 62 exact statements and transitive reports. It constructs the multiplier
from a uniform variable, proves its exact CDF, derives product-law entropy
and residual-tail bounds, and proves the full factor-32 selection comparison.
The [light-contraction constant audit](light-contraction-constant-20261121/README.md)
of 21 November 2026 adds the paper's intermediate constants: the band masses,
the first summand below $192$, $C_V<256$ and the two inverse moments.

The [sign-neutral tail-test audit](arbitrary-law-tail-test-20261110/README.md)
adds 91 exact statements and transitive reports for the single-coin test of
the tail certificate: its work cap, flip symmetry and sign-neutral law, both
unresolved-probability bounds, the multiplier comparison and the expected-work
bound. Inverse sampling and the pilot are not part of it.

The [capped tail-probe audit](arbitrary-law-tail-probe-20261110/README.md)
adds 69 exact statements and transitive reports for one probe of the tail
certificate's inverse-sampling step: its caps and charge, dependence on the
bought flips, coverage at every budget with probability at least 7/8, and the
fixed-budget performance bound with probability at least 3/4. The median over
probes, the oracle comparison and the pilot are not part of it.

The [tail-median audit](arbitrary-law-tail-median-20261111/README.md) adds 51
exact statements and transitive reports for the median over independent
probes: the majority transfer to the median, Hoeffding across probes,
statement (1) of the tail certificate with its pathwise flip cap, the
statement at every depth at once, and both on a single coin array. The oracle
comparison and the pilot are not part of it.

The [tail-oracle audit](arbitrary-law-tail-oracle-20261111/README.md) adds 26
exact statements and transitive reports for the oracle comparison of the tail
certificate: the kernel bounds, the split of the gap law at its quantile, the
onset condition and its existence, and the bound of the median by 524288 times
the selection functional. The pilot is not part of it.

The [tail-observable audit](arbitrary-law-tail-observable-20261111/README.md)
adds 68 exact statements and transitive reports for the tail certificate in
the observable experiment: a reader that runs the probes from observed flips,
the certificate as a function of the observed word, the transfer of events
about that word to the law of the original experiment, and statements (1) and
(3) for the estimator's output with coverage at every pause. The estimator
buys every block in full. The pilot is not part of it.

The [pilot audit](arbitrary-law-pilot-20261111/README.md) adds 66 exact
statements and transitive reports for the capped multi-depth pilot of the
adaptation proof: its budgets and caps, the event (A8) at every depth at once
with a common number of probes, the pilot installed in the paid learning
stage, and the learned law (A9), which dominates the gap law on that event.
The learned law's comparison with the oracle is not part of it.

The [pilot-onset audit](arbitrary-law-pilot-onset-20261111/README.md) adds 25
exact statements and transitive reports for the first part of that
comparison: the lowest-gap split of the gap law, the pilot's work estimates
(A12), its onset, and the bounds of the work and of the coin cap by the
selection functional. The learned-CDF bound and the final comparison are not
part of it.

The [learned-oracle audit](arbitrary-law-learned-oracle-20261111/README.md)
adds 31 exact statements and transitive reports for the rest of that
comparison: the learned-CDF bound (A13), the slack bound (A14), the
clipped-CDF witness, and the comparison (A11) of the learned law with the
oracle, with factor $2^{24}$ past a finite onset, on the pilot event. The
robust continuation is not part of it.

The [zero-quantile audit](arbitrary-law-zero-quantile-20261112/README.md) adds
22 exact statements and transitive reports for (A16): the quantile design of
a law with mass at zero, the comparison $Q_\alpha\le4K_\alpha$ with the
selection functional, and the converse. The planner that uses the design is
not part of it.

The [known-law planner audit](known-law-planner-20261112/README.md) adds 49
exact statements and transitive reports for the plan of the known-law
estimator: its level races and level price, its cap search, its counts, and
the validity of its squared-error certificate for every admissible plan. The
price is that of the checked upper theorem. The plan's rate and the toolkit's
own price are not part of it.

The [plan-rate audit](known-law-plan-rate-20261112/README.md) adds 18 exact
statements and transitive reports for the rate of that plan with the exact
integrals of the quantile split: the smaller of $\rho/2$ and its certified
risk is at most $(1+\tfrac85\max\{2048,28000\sqrt\theta\})$ times the
selection functional, and its reported radius at most six times that. The
rate of a plan computed from upper bounds is not part of it.

The [tight-rate audit](known-law-plan-tight-rate-20261112/README.md) adds 31
exact statements and transitive reports for the rate of that plan computed
from upper bounds within a factor two, for a law of positive gaps and for a
reference law with mass at zero. For dyadic weights the smaller of $\rho/2$
and the certified risk of the latter is at most $C_0K_\alpha$ with
$C_0=1+4\max\{4096,8\sqrt2\cdot28000\}$, and the reported radius at most
$6C_0K_\alpha$. These are statements about the plan's certificate; an
experiment with coins of gap zero is not part of it.

The [planner-output audit](known-law-planner-output-20261112/README.md) adds
9 exact statements and transitive reports for the planner end to end: the
quantile split is constructed for every law of positive gaps, and the
minimax risk is at most $44801$ times the selection functional with exact
integrals, and the factor-two coefficient for every tight enclosure. Those
minimax statements name no estimator and already follow from the $28000$
upper theorem. The [planner-estimator audit](known-law-planner-estimator-20261114/README.md)
adds 8 exact statements and transitive reports in which the estimator the
planner returns, the plan or the constant $\rho/2$, is named: it has budget
$B$ and risk at most $44801$ times the selection functional with exact
integrals, and the factor-two coefficient for every tight enclosure.

The [dyadic-summability audit](dyadic-summability-20261114/README.md) adds 7
exact statements and 5 transitive axiom reports proving that the two dyadic series of
the frozen targets H3 and H4 converge. Those frozen targets bound `∑'` sums,
which Mathlib sets to zero for a series that does not converge.

The [robust-error audit](robust-error-transfer-20261113/README.md) adds 33
exact statements and transitive reports for the first part of the robust
continuation: the raced classifier is monotone in the flips, its error on
one coin does not increase with the gap, and its population error under a
true law coupled above the reference is at most the reference bound plus
the uncoupled mass. The coupling is a hypothesis, and the work of the race
is not part of it.

The [robust-work audit](robust-coin-work-20261113/README.md) adds 9 exact
statements and transitive reports for the work of the race on one coin: the
ordinary, negative-bank and positive-bank bounds of the known-law theorem
hold at a reference gap for a coin of every larger gap. The level work
under a coupling is not part of it.

The [robust-level audit](robust-level-certificates-20261113/README.md) adds
18 exact statements and transitive reports for the two certificates of a
level race under a true law coupled above its reference: its expected work
is at most the level-work certificate of the known-law theorem with the
uncoupled mass added to the unresolved mass, and its error at most
$\delta_l$. The bank's null law is the positive part of the reference, so a
reference with mass at zero needs no coin of gap zero. The coupling in that
form is a hypothesis, and the corrections and the plan under the true law
are not part of it.

The [robust-plan audit](robust-plan-20261114/README.md) adds 20 exact
statements and transitive reports for the plan of a reference law under the
true law. An admissible plan spends at most the budget and has
root-mean-square risk at most the square root of its certificate, and one
estimator, fixed by the reference $\alpha$, has risk at most $C_0K_\alpha$
under every true law coupled above $\alpha$. The coupling is a hypothesis;
the capped median and the connection to the paid stage are not part of it.

The [CDF-to-continuation record](robust-cdf-bridge-20261116/README.md)
checks 12 exact statements and 12 transitive axiom reports: the increasing
coupling constructed from CDF domination, its positive-reference and
zero-atom split, preservation of the original sign mass and rarity budget,
and the named plan's budget/risk certificate and uniform reference-law
rate directly under CDF domination. Its local project audit covers the
364-module import closure; it does not claim a whole-project kernel replay
or the conditional capped median and paid-stage composition.

The [clipping and pilot-independence record](clipping-pilot-independence-20261116/README.md)
checks 26 exact statements and transitive axiom reports. It covers the
clipped estimator's unchanged experiment and work, risk contraction and
bounded CDF planner, and the joint and conditional law of the complete
production stream and private seed after the paid adaptive pilot. It also
identifies the observed pilot word jointly with the interval in the
original experiment and fixes the learned law inside the conditional
continuation. Its scope ends before conditional capped-median coverage.

The [paid-median record](paid-median-20261116/README.md) adds 48 exact
statements and transitive reports. It selects a robust reference base for
every supported probability law, including large zero atoms, and proves
conditional capped-median coverage given a valid paid pilot prefix. The
concrete installed stage has unconditional failure at most `epsilon + delta`,
a cap including the pilot on every path, and a deterministic reported-radius
bound. The final guarantee is under the original hidden-gap experiment and
assumes no continuation-risk oracle. Finite-law numerical enclosures,
the complete all-budget controller and Python execution remain separate.

The [full arbitrary-law controller record](arbitrary-law-controller-20261116/README.md)
adds 99 exact statements and transitive reports for the concrete procedure
and final theorem of #83. One event gives all-budget coverage and eventual
oracle width for every positive-gap probability law and globally rare sign
allocation, with unconditional work caps and consistent observable prefixes.
The record identifies its proof checkpoint and 730-module project closure.
The historical component records keep their earlier scope.
