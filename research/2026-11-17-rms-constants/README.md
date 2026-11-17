# RMS constants, oracle efficiency and finite stopping caps

These notes review the mathematics of the [v6 manuscript](../../paper/v6/README.md) at commit `97a5013`.

| Proof | Result | Evidence |
|---|---|---|
| [First review](adaptive-threshold-math-review.pdf) · [TeX](adaptive-threshold-math-review.tex) | The ordinary RMS lower coefficient exceeds 0.1332. Midpoint regularization yields a square-root cap comparison and the factor-two test at $4B/9$. A separate affinity argument bounds the infinite stopping program by $3\sqrt7/2$ times minimax risk. | Paper derivations. The square-root cap comparison and its $4B/9$ factor-sixteen corollary also have a Lean proof. |
| [Second review](adaptive-threshold-second-review.pdf) · [TeX](adaptive-threshold-second-review.tex) | The universal RMS lower coefficient exceeds 0.152799. At four flips the deterministic-sign experiment has minimax RMS exactly $1/6$. For the two magnitude oracles and finite $I=\mathbb E[1/D]$, the large-budget RMS constant is $I/4$, and the unbiased variance–work optimum is $I^2/16$. | Paper proofs. The revealed oracle can inspect its iid magnitude array for free. For the ordinary hidden-gap model the asymptotic lower bound holds generally and this construction gives equality at a single gap. |
| [Narrowing the universal RMS constant](rms-gap.pdf) · [TeX](rms-gap.tex) | The unrestricted coefficient exceeds 0.16207250 and is at most $1/6$. The coefficient is exactly $1/6$ for budgets through four, for protocols with at most three flips per coin, and for the two classes with unlimited revisits described below. | Paper derivations with an [exact interval certificate](check_gap.py) and an [exhaustive stopping-tree certificate](check_three_flips.py). |

At unrestricted budgets the three-flip result allows adaptive revisiting and interleaving. With unlimited revisits, the same sharp bound holds when the list of coins and each coin's local stopping rule are chosen before any outcomes are observed. It also holds when sign-symmetric local rules are chosen adaptively and run one coin at a time. A four-flip stopping rule violates the pointwise information inequality used in the three-flip proof. The universal coefficient for unrestricted adaptive protocols remains open.

The [cap proof](SharpCap.lean) imports the repository's ordinary and genie program definitions. Its [two exact statement checks](AuditSharpCap.lean) and [audit record](audit.json) cover compilation, transitive axioms and kernel replay of the new module. The cached checkout at `9927628` and the reviewed commit have identical `lean/` Git trees. The audit reuses compiled dependencies.

From the repository root, with Python, SymPy and the pinned Lean toolchain available, run

```sh
P=research/2026-11-17-rms-constants
python "$P/check.py"
python "$P/check_second_review.py"
python "$P/check_gap.py"
python "$P/check_three_flips.py"
(cd lean && lake build ThresholdHC.GenieRate.Flow ThresholdHC.Genie.OptimizedBrackets)
python "$P/verify_cap.py" .
```

The price certificate covers 303,086 boxes and bounds the final integral on 65,536 intervals using outward-rounded integer arithmetic. The stopping-tree certificate checks all 25 active trees of depth at most three on 34 polynomial cones and computes the exact excess at depth four. The statistical arguments are in the linked notes.
