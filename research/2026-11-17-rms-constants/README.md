# RMS constants, oracle efficiency and finite stopping caps

These notes review the mathematics of the [v6 manuscript](../../paper/v6/README.md) at commit `97a5013`.

The [sharp unrestricted theorem](sharp-unrestricted.pdf) gives the exact universal RMS coefficient **$1/6$** for the ordinary model and both magnitude oracles, with arbitrary adaptive revisits, interleaving, and uniform expected budgets. At each budget the infimum of the normalized risk over gap laws is attained by a single gap. The proof uses three sign biases for large budgets and an [exact arithmetic certificate](check_budget_window.py) in an intermediate range. [TeX source](sharp-unrestricted.tex)

| Proof | Result | Evidence |
|---|---|---|
| [First review](adaptive-threshold-math-review.pdf) · [TeX](adaptive-threshold-math-review.tex) | The ordinary RMS lower coefficient exceeds 0.1332. Midpoint regularization yields a square-root cap comparison and the factor-two test at $4B/9$. A separate affinity argument bounds the infinite stopping program by $3\sqrt7/2$ times minimax risk. | Paper derivations. The square-root cap comparison and its $4B/9$ factor-sixteen corollary also have a Lean proof. |
| [Second review](adaptive-threshold-second-review.pdf) · [TeX](adaptive-threshold-second-review.tex) | The universal RMS lower coefficient exceeds 0.152799. At four flips the deterministic-sign experiment has minimax RMS exactly $1/6$. For the two magnitude oracles and finite $I=\mathbb E[1/D]$, the large-budget RMS constant is $I/4$, and the unbiased variance–work optimum is $I^2/16$. | Paper proofs. The revealed oracle can inspect its iid magnitude array for free. For the ordinary hidden-gap model the asymptotic lower bound holds generally and this construction gives equality at a single gap. |
| [Narrowing the universal RMS constant](rms-gap.pdf) · [TeX](rms-gap.tex) | The unrestricted coefficient exceeds 0.16207250 and is at most $1/6$. The coefficient is exactly $1/6$ for budgets through four, for protocols with at most three flips per coin, and for the two classes with unlimited revisits described below. | Paper derivations with an [exact interval certificate](check_gap.py) and an [exhaustive stopping-tree certificate](check_three_flips.py). |

The three-flip result in the earlier note allows adaptive revisiting and interleaving. With unlimited revisits, that note also covers preassigned local stopping rules and sequentially chosen sign-symmetric rules. Its four-flip example violates the pointwise information inequality used in the three-flip proof. The sharp unrestricted theorem above uses a different inequality.

The [cap proof](SharpCap.lean) imports the repository's ordinary and genie program definitions. Its [two exact statement checks](AuditSharpCap.lean) and [audit record](audit.json) cover compilation, transitive axioms and kernel replay of the new module. The cached checkout at `9927628` and the reviewed commit have identical `lean/` Git trees. The audit reuses compiled dependencies.

From the repository root, with Python, SymPy and the pinned Lean toolchain available, run

```sh
P=research/2026-11-17-rms-constants
python "$P/check.py"
python "$P/check_second_review.py"
python "$P/check_gap.py"
python "$P/check_three_flips.py"
python "$P/check_budget_window.py"
(cd lean && lake build ThresholdHC.GenieRate.Flow ThresholdHC.Genie.OptimizedBrackets)
python "$P/verify_cap.py" .
```

The price certificate covers 303,086 boxes and bounds the final integral on 65,536 intervals using outward-rounded integer arithmetic. The stopping-tree certificate checks all 25 active trees of depth at most three on 34 polynomial cones and computes the exact excess at depth four. The statistical arguments are in the linked notes.

For the sharp unrestricted theorem, the standard-library checker covers 140 bias intervals and bounds a one-dimensional integral on 2,048 bins at each accepted upper endpoint. An analytic bound covers all exit barriers of height 20 and above. The [Lean integer proof](SharpWindow.lean) checks all 140 intervals by kernel reduction. The [middle-budget proof](SharpMiddleBudget.lean) connects their rectangle sums to the Fisher-information integral and proves the critical point-mass lower bound at every budget $B\ge4$.

For every gap law and every expected budget $0\le B\le4$, the [small-budget Lean theorem](SharpFourBudget.lean) gives $R_\mu(B)\ge 1/6$ for unrestricted adaptive estimators. Its proof integrates the [exact Bayes risk at each leaf](SharpSmallBudget.lean) against the uniform prior and accounts for [distinct queried signs on each adaptive transcript](SharpSmallPrefix.lean). It averages over the seed and the hidden gaps and passes to the limit under finite expected work. At the endpoint it proves $R_{\delta_{1/2}}(4)=1/6$.

The [four-flip Lean construction](SharpAttainment.lean) proves uniform budget four, exact squared risk $1/36$ at every sign law for the endpoint gap, and an upper bound of $1/6$ on the original minimax risk. The [testing theorem](SharpEntropy.lean) handles any measurable real-valued output under three probability laws, subject to the stated reverse-KL bound. For every finite horizon, arbitrary adaptive coin labels and a common flip bias, Lean proves the [fair-posterior work identity](SharpTranscript.lean) and the [summed reverse-KL bound](SharpPrefixCost.lean) for $0<s\le 2/5$ and $s^2 B=4$. The [scalar price proof](SharpInformation.lean) uses derivatives and exact rational comparisons.

For a point mass at the critical gap $d=1/\sqrt B$ and every $B\ge25$, Lean proves the stronger minimax lower bound $\sqrt{59/2100}\approx 0.16761634$. The [finite risk inequality](SharpWeakRisk.lean) is linear in the three risks and the expected work under the fair law. The [population proof](SharpWeakPopulation.lean) averages it over the algorithm's random seed and uses eventual reconstruction of the stopped tape to pass to unbounded stopping. The [local simulation lemma](SharpSimulation.lean) checks the one-step probability and posterior-lattice constraint. For $4<B\le6400/1521$, the [near-perfect critical-gap theorem](SharpCriticalBudget.lean) proves $R_{\delta_d}(B)\ge 1/6$ at $d=1/\sqrt B$. It combines the [weighted score inequality](SharpScore.lean), a [Fisher-information bound on adaptive transcripts](SharpAdaptivePrice.lean), and an [analytic integral bound](SharpPriceBounds.lean) for $39/40\le 2d<1$. The same population theorem takes an admissible integrated price as input at any $0<2d<1$.

The [unrestricted ordinary-model theorem](SharpUnrestricted.lean) proves $R_\mu(B)\ge\omega/6$ for every gap law and every $B\ge1$, where $\omega=\int\min(1,B^{-1/2}/d)\,\mu(dd)$. The [single-coin simulation](SharpSingleTape.lean) has the target tape law on every binary cylinder. The [population simulation](SharpPopulationTransfer.lean) implements it causally under any adaptive policy. It [preserves expected work and rescales RMS risk exactly](SharpReduction.lean), including infinite squared error. This also proves $R_\mu(B)\ge\omega\sqrt{59/2100}$ for every $B\ge25$. The endpoint equality makes $1/6$ the largest coefficient valid simultaneously at all budgets.

For both magnitude oracles, the [oracle reduction](SharpOracleReduction.lean) allows an arbitrary measurable array of magnitudes conditional on the oracle seed. This covers free inspection of the entire iid gap array and a magnitude selected adaptively at each creation. Lean proves the [same two lower bounds](SharpOracleBounds.lean) and [exact endpoint equality](SharpOracleAttainment.lean) in each model. The selected-oracle proof shows that naming a fresh coin by its birth history preserves the distribution of the four observed flips.

These proofs are also in the audited library, as [`lean/ThresholdHC/SharpRMS`](../../lean/ThresholdHC/SharpRMS/Specification.lean) and [`lean/ThresholdHC/SquareRootCap`](../../lean/ThresholdHC/SquareRootCap/Specification.lean). CI builds them, [`tools/verify_sharp_rms.py`](../../tools/verify_sharp_rms.py) and [`tools/verify_square_root_cap.py`](../../tools/verify_square_root_cap.py) audit their statements and axioms, and the definition lock pins their definitions. The [library record](../../results/sharp-rms-20261117/README.md) maps each library module to the file of this package it was derived from. The files and records below remain the research checkpoint.

## The coefficient for budgets of at least 25

Write $c_{25}$ for the largest ordinary-model coefficient such that $R_\mu(B)\ge c_{25}\,\omega_\mu(B^{-1/2})$ for every gap law and every real $B\ge25$. The certified interval is

$$
0.175198\ \le\ c_{25}\ \le\ 0.186752.
$$

The lower endpoint also applies to the revealed- and selected-magnitude oracles. For $B\ge100$ the lower coefficient increases to $0.17807955$. The sharp value for $B\ge25$ remains open. [Lower theorems](MultiBiasBounds.lean) · [Adaptive upper witness](PilotWitness.lean) · [Lower-bound statements](AuditMultiBias.lean) · [Kernel replay](multi-bias-audit.json)

At the critical gap $d=B^{-1/2}$, write $s=2d$ and let $P_t$ be the transcript law at sign mean $t$. The summed reverse divergences from $P_0$ to $P_{\pm t}$ are at most $-\log(1-t^2s^2)\,\mathbb E_0 W$ when $t^2\le2/3$. This follows by bounding the log likelihood of each sampled coin in terms of its posterior and applying the Wald identity. For $t=29/40$, the earlier three-bias test then gives the following sufficient condition on a positive RMS coefficient $r$, with $k=11774928000/2595112129$ and $b=29/4$.

$$
4(k+2b)r^2\ \le\ 2.7401+2(1-1/8)+B\log(1-4t^2/B).
$$

The right side increases with $B$. The proof checks the logarithm at the cutoff with a finite rational Taylor sum, averages over private randomness and passes to unbounded stopping under the original expected-work budget. [Entropy per flip](LargeBudgetTranscript.lean) · [Three-bias inequality](LargeBudgetTest.lean) · [Population risk](LargeBudgetPopulation.lean) · [Budget dependence](LargeBudgetPrice.lean)

The stronger lower bound uses the fair-sign law together with five pairs of alternatives $\pm t_i$, where the positive biases are $0.527436$, $0.679980$, $0.753283$, $0.798023$ and $0.816490$. For a clipped estimate $x$ of the sign mean, each alternative uses a positive test $1+b_i((x-t_i)^2-R)$, where $R=4(0.175198)^2$. If the mean squared error is at most $R$ under that alternative, its expected test value is at most one. All ten logarithmic tests can therefore be bounded using divergence from the same fair law. Their sum and a positive multiple of $x^2$ give a pointwise lower bound for every $|x|\le1$. Lean verifies it using a degree-27 Taylor lower bound for the exponential and exact polynomial checks on nine intervals in $x^2$. [Test coefficients](MultiBiasData.lean) · [Scalar certificate](MultiBiasCertificate.lean) · [Finite-transcript inequality](MultiBiasPrefix.lean)

Write $P(B)=-B\sum_i\log(1-4t_i^2/B)$, $a=19.780099$ and $g_{i,t}(x)=1+b_i((x-t)^2-R)$. The pointwise inequality checked by Lean is

$$
a x^2+\sum_i\bigl(\log g_{i,t_i}(x)+\log g_{i,-t_i}(x)\bigr)\ \ge\ aR+P(25).
$$

If all eleven sign-mean squared errors are at most $S$, the fair-law expectation of the left side is at most $aS+P(B)+2\sum_i b_i(S-R)$. Comparing these two bounds gives the following RMS coefficient at each real $B\ge25$, with $D=a+2\sum_i b_i=93.534911$.

$$
\frac12\sqrt{R+\frac{P(25)-P(B)}{D}}.
$$

The factor of two converts sign mean to positive-sign fraction. $P(B)$ decreases with $B$, which yields both reported cutoffs. The proof averages over private randomness and uses finite expected work to pass from finite transcripts to the stopped experiment. The single-gap reduction then gives the result for every gap law in each of the three models. [Budget calculation](MultiBiasPrice.lean) · [Stopping and randomization](MultiBiasPopulation.lean) · [Uniform lower bounds](MultiBiasBounds.lean)

The earlier fixed-sample upper bound takes $B=25$ and $\mu=\delta_{1/5}$, where the modulus equals one. The protocol queries 25 distinct coins once each and returns a rational estimate indexed by the head count. When the positive-sign fraction is $p$, each observation has head probability $3/10+2p/5$. The mean squared error is a degree-13 polynomial in $(2p-1)^2$. Four exact Bernstein expansions certify that it is at most $0.195454^2$ on the full parameter interval. [Fresh-flip law](LargeBudgetFresh.lean) · [Estimator and polynomial certificate](LargeBudgetTable.lean)

The 20-flip pilot uses the same gap and a hard cap of 25 flips. Flip 20 distinct coins and let $j$ be the number of heads. For $5\le j\le9$, revisit five distinct coins that showed heads. For $11\le j\le15$, revisit five that showed tails. In the other cases use five fresh coins. The estimate depends on $j$ and the head count among the final five flips. [Policy](RevisitPolicy.lean) · [Estimator table](RevisitCertificate.lean)

If the positive-sign fraction is $p$, a fresh head has probability $b=(3+4p)/10$. A previously observed head has repeat-head probability $(9+40p)/(100b)$, and a previously observed tail has repeat-head probability $21/(100(1-b))$. Since the five chosen labels are distinct, their outcomes are conditionally binomial given the pilot. Lean proves this from the original transcript likelihood. It checks the resulting risk polynomial over the full interval by exact integer arithmetic and gives RMS at most $0.188087$. [Conditional law](RevisitHistory.lean) · [Two-stage expectation](RevisitExperiment.lean) · [Squared-risk proof](RevisitRisk.lean) · [Exact statements](AuditRevisit.lean) · [Replay record](revisit-audit.json)

The $0.186752$ upper bound uses 18 fresh flips at the same critical gap. Let $j$ be their head count. At follow-up position $k=0,\ldots,6$, the decision depends on $j$ and all $k$ earlier follow-up answers. It can request a fresh coin, the $(k+1)$st pilot head, or the $(k+1)$st pilot tail, in pilot order. A missing candidate defaults to fresh. For example, after eight pilot heads, the rule revisits the first head. If that flip is tails, it revisits the second head next. If it is heads, it flips a fresh coin next. Distinct positions always select distinct labels during the follow-up. To find the rule, we minimized Bayes squared loss backwards through the seven choices under a symmetric four-point prior on $0,x,1-x,1$, with $x\approx0.298645$ and total endpoint mass about $0.392448$. The terminal estimate is a rational number with denominator 100,000. [Policy and history law](PilotPolicy.lean) · [Actions and estimates](PilotTable.lean)

The suffix expectation obeys a binary recursion. When it queries a pilot coin, the likelihood replaces the single observed flip by the joint probability of the pair. For example, two heads contribute $(9+40p)/100$, and a head and a tail contribute $21/100$ in either order. After summing over the 19 pilot counts, Lean compares the risk polynomial to its endpoint value on eight rational subintervals covering $[0,1]$. The exact worst squared error of this protocol is $348763093753675683898541718818533/10^{34}$, attained at both $p=0$ and $p=1$. Its square root is approximately $0.186751999656$. [Experiment](PilotExperiment.lean) · [Likelihood polynomial](PilotPolynomial.lean) · [Interval certificate](PilotCertificate.lean) · [Exact statements](AuditPilot.lean) · [Kernel replay](pilot-audit.json)

## Reproducing the formal checks

The [ordinary](AuditSharpUnrestricted.lean) and [oracle](AuditSharpOracles.lean) statement audits check these inequalities against the original definitions. The [critical-window audit](AuditSharpWindow.lean) and [earlier component checks](AuditSharpRMS.lean) give the intermediate statements. The [ordinary-model verification record](sharp-unrestricted-audit.json) covers 38 proof modules and six exact statement checks. The [oracle verification record](sharp-oracles-audit.json) covers all 44 proof modules and checks four oracle statements. A [second oracle record](sharp-oracles-linux-audit.json) repeats that check on Linux; its `procedure` field says how it differs from running `--oracles`. Each run rebuilt the listed research modules from source against the compiled project and Mathlib dependencies. The [critical-window record](sharp-critical-window-audit.json) covers 27 modules, and the [earlier component record](sharp-rms-audit.json) covers 18. Each records the source hashes and transitive axioms. To replay the unrestricted proof from a built checkout with the same Lean source tree, run

```sh
(cd lean && lake build ThresholdHC.HardBudget.Application ThresholdHC.Tier5.CreationFresh \
  ThresholdHC.ContinuousObserved.UniformTape ThresholdHC.ObservableSimulation.OriginalExperiment \
  ThresholdHC.ContinuousObserved.Prefix ThresholdHC.Tier6.Full ThresholdHC.OracleLower.Realization)
python research/2026-11-17-rms-constants/verify_sharp_rms.py . --unrestricted
python research/2026-11-17-rms-constants/verify_sharp_rms.py . --oracles
python research/2026-11-17-rms-constants/verify_sharp_rms.py . --large-budget
python research/2026-11-17-rms-constants/verify_sharp_rms.py . --revisit
python research/2026-11-17-rms-constants/verify_sharp_rms.py . --pilot
python research/2026-11-17-rms-constants/verify_sharp_rms.py . --multi-bias
```
