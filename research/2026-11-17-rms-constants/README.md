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

For the sharp unrestricted theorem, the standard-library checker covers 140 bias intervals and bounds a one-dimensional integral on 2,048 bins at each accepted upper endpoint. An analytic bound covers all exit barriers of height 20 and above. The full unrestricted lower bound is a paper proof with this computational step.

For every gap law and every expected budget $0\le B\le4$, the [small-budget Lean theorem](SharpFourBudget.lean) gives $R_\mu(B)\ge 1/6$ for unrestricted adaptive estimators. Its proof integrates the [exact Bayes risk at each leaf](SharpSmallBudget.lean) against the uniform prior and accounts for [distinct queried signs on each adaptive transcript](SharpSmallPrefix.lean). It averages over the seed and the hidden gaps and passes to the limit under finite expected work. At the endpoint it proves $R_{\delta_{1/2}}(4)=1/6$.

The [four-flip Lean construction](SharpAttainment.lean) proves uniform budget four, exact squared risk $1/36$ at every sign law for the endpoint gap, and an upper bound of $1/6$ on the original minimax risk. The [testing theorem](SharpEntropy.lean) handles any measurable real-valued output under three probability laws, subject to the stated reverse-KL bound. For every finite horizon, arbitrary adaptive coin labels and a common flip bias, Lean proves the [fair-posterior work identity](SharpTranscript.lean) and the [summed reverse-KL bound](SharpPrefixCost.lean) for $0<s\le 2/5$ and $s^2 B=4$. The [scalar price proof](SharpInformation.lean) uses derivatives and exact rational comparisons.

For a point mass at the critical gap $d=1/\sqrt B$ and every $B\ge25$, Lean proves the stronger minimax lower bound $\sqrt{59/2100}\approx 0.16761634$. The [finite risk inequality](SharpWeakRisk.lean) is linear in the three risks and the expected work under the fair law. The [population proof](SharpWeakPopulation.lean) averages it over the algorithm's random seed and uses eventual reconstruction of the stopped tape to pass to unbounded stopping. The [local simulation lemma](SharpSimulation.lean) checks the one-step probability and posterior-lattice constraint. The transfer from a critical gap to arbitrary gap laws for $B>4$ and the critical-gap lower bound for $4<B<25$ still require a formal proof.

The [exact theorem statements](AuditSharpRMS.lean) and [kernel replay record](sharp-rms-audit.json) cover these components. To reproduce the record from a built checkout with the same Lean source tree, run

```sh
(cd lean && lake build ThresholdHC.HardBudget.Application ThresholdHC.Tier5.CreationFresh)
python research/2026-11-17-rms-constants/verify_sharp_rms.py .
```
