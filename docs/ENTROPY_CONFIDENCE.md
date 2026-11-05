# The sharper general-law confidence coefficient

For every known positive-gap probability law, $0<\rho\le1/4$,
$B>0$ and $0<\delta\le1/4$, put $\beta=B/\log(1/\delta)$.
The checked comparison is

\[
10^{-17}Q(\beta)\le r_{\rm exp}(B,\delta)
\le r_{\rm hard}(B,\delta)\le750000\,\mathcal K(\beta).
\]

Since $\mathcal K\le Q$, the lower coefficient also applies to the
entropy–tail functional. The theorem uses the original observable
adaptive experiment and allows unbounded stopping under its uniform
expected-work constraint.

## Direct stopping-program comparison

Write $P=P_\infty(b)$ at any positive budget $b$.
For retained prefix entropy $F$, put
$M=\min\{\rho,\sqrt{\rho F/b}\}$.

The existing packing theorem and annular certificate estimate give

\[
M\le256\left(256b_C+\sqrt{16384e^{48}V_C}\right)
\le256\cdot6\cdot10^{12}\sqrt{b_C^2+V_C}.
\]

At every positive cap, an attained certificate has
$\sqrt{b_C^2+V_C}=P_N(b)$. Taking the cap infimum proves
$M\le16\cdot10^{14}P$. The bounded-entropy and failed-cutoff
branches satisfy the same bound, using the label and quantile-tail
lower estimates.

The tail modulus satisfies $T\le32P$. The deterministic comparison
$Q(b)\le T+2M$ therefore gives

\[
30\cdot10^{-17}Q(b)\le P_\infty(b),
\]

because $30\cdot10^{-17}(32+32\cdot10^{14})<1$.
Combining this inequality at $b=\beta$ with the stopped confidence
bound $P_\infty(\beta)/30$ gives the coefficient $10^{-17}$.

## Proof map

| Step | Native proof |
|---|---|
| Retained-core bound at the exact program infimum | [Core](../lean/ThresholdHC/ConfidenceEntropy/Core.lean) |
| Closed-quantile comparison in all cutoff cases | [Program](../lean/ThresholdHC/ConfidenceEntropy/Program.lean) |
| Closed-quantile and entropy–tail confidence lower bounds, estimator consequence and full law | [Full](../lean/ThresholdHC/ConfidenceEntropy/Full.lean) |

The [native record](../results/entropy-confidence-20261105/README.md)
checks six exact statements and six transitive axiom reports.
The [manuscript proof](../paper/v6/entropy-confidence.tex) gives the
constants and the cap-infimum argument.

## Scope

The stopping-program comparison supplies the stronger general-law
coefficient directly. The separately checked
[fractional-submeasure theorem](ADDITIVE_CONFIDENCE.md) retains
its explicit component variance–null-work premises.

The sharp quantile-factor characterization remains a paper proof.
The law-dependent time-uniform lower bound, unknown-law oracle-rate
adaptation, unrestricted exact-selection complexity and optimal cap
convergence rate remain open research. Human specialist review is
absent, as recorded in the project scope.
