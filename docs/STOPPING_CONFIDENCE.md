# A confidence lower bound from the stopping-program dual

Let $\ell=\log(1/\delta)$, $0<\delta\le1/4$ and $\beta=B/\ell$.
For any positive-gap probability law, $0<\rho\le1/2$ and $B>0$, the
uniform expected-budget confidence radius satisfies
$$
 r^{\rm exp}_{\mu,\rho}(B,\delta)\ \ge\ P_\infty(\beta)/30 .
$$
Here $P_\infty$ is the [unrestricted stopping-program value](../paper/v6/appendix-genie.tex).
For $0<\rho\le1/4$, the [direct retained-entropy comparison](ENTROPY_CONFIDENCE.md)
now gives $30\cdot10^{-17}Q(\beta)\le P_\infty(\beta)$.
Consequently the checked general-law lower coefficient is $10^{-17}$
for both the closed-quantile and entropy–tail functionals.
The [earlier paper](../research/2026-10-30-confidence-transfer/NOTE.md)
also obtains this coefficient by additive localization.

## Local information and paid work

For two priors $q,r$, let $m=(q+r)/2$, $s=(3q+r)/4$, and
$t=(q+3r)/4$. Use $h=1-\int\sqrt{dP\,dQ}$ for squared Hellinger
distance. If every capped observable one-coin rule has midpoint
information/work ratio at most $J$, its stopped words satisfy
$h(P_q,P_r)\le J W_m/4$. This follows from
$(\sqrt{x}-\sqrt{y})^2\le(x-y)^2/(x+y)$ and includes the seed in the
transcript. [Ordered stopping inequality](../lean/ThresholdHC/StoppingProgram/OrderedInformationBound.lean)

The single-coin experiment is affine in its prior, so $W_m\le2W_s$.
This holds even if the coin's sign strongly affects its stopping time.
In a finite population tree, simulate all other coins under $s$ when
isolating one slot. They supply independent randomness for that local
rule. Its Hellinger loss is bounded by $J/2$ times the expected work on
that slot under $s$. The quarter-smoothing lemma gives local KL at most
$8/3$ times the Hellinger loss. The one-slot hybrid identity adds these
KL contributions under the same reference law. Their work sums to the
number of flips actually purchased. Consequently the full observable
KL between $s$ and $t$ is at most $(4/3)JB$ under a uniform budget
$B$. Passing to stopped transcripts uses their finite-prefix
reconstruction and finite expected work at both endpoints.

## Separation at the effective budget

In the exact four-prior dual for $P_\infty(\beta)^2$, take a quartet
with positive target gap $\Delta$ and finite ratio $K_\infty$. Its
contribution is $\Delta^2/(4+\beta K_\infty)$. Quartets of zero value
satisfy the desired bound directly. Absorb the variance and work priors
into both endpoints, with the original endpoint receiving weight $1/3$.
The midpoint ratio is at most $K_\infty$ at every cap, and the gap is
$\Delta/3$. Contract each endpoint toward its common midpoint by
$a=(1+6\beta K_\infty)^{-1/2}$. This preserves rarity and the midpoint,
multiplies the separation by $a$, and multiplies the midpoint information
by $a^2$. [Reference absorption](../lean/ThresholdHC/StoppingProgram/AbsorptionRatio.lean)
and [contraction](../lean/ThresholdHC/StoppingProgram/PriorContraction.lean)

Apply the local argument to the contracted pair. The final quarter
mixtures have target separation $a\Delta/6$ and KL at most
$(4/3)a^2 K_\infty B\le 2\ell/9$. A uniformly valid radius
$\varepsilon<a\Delta/12$ would, by testing the two separated means,
require KL at least $\ell/4$. Hence $\varepsilon\ge a\Delta/12$.
Since $144(1+6x)\le900(4+x)$ for $x\ge0$, this gives
$\Delta^2/(4+\beta K_\infty)\le(30\varepsilon)^2$.
Taking the dual supremum and the infimum over observable procedures
proves the assertion. The direct bound
$30\cdot10^{-17}Q(\beta)\le P_\infty(\beta)$ gives the sharper
entropy–tail consequence. [Explicit comparison](ENTROPY_CONFIDENCE.md)

## The matching hard-cap upper bound

Run $k=2m+1$ independent copies at expected budget $b=B/(8k)$, with
$\lfloor B/k\rfloor$ reservations each. A timeout costs at least one more
flip in the uncapped run, so its probability is at most $1/8$ even if
the reservation is zero. The probability of completion with error greater
than $\sqrt8$ times the base RMS is at most $1/8$. If the median fails,
at least $m+1$ copies fail. For failure indicators $I_i$, Markov's inequality
applied to the product of the factors $1+2I_i$ gives probability at most
$(3/4)^m/2$. This uses independence across copies. The observable median
accepts a stop after the final allowed flip and spends at most $\lfloor B\rfloor$
on every valid path. [Controller](../lean/ThresholdHC/ConfidenceProgram/MedianController.lean)
and [amplification](../lean/ThresholdHC/ConfidenceProgram/Amplify.lean)

With $m=\lceil4\ell\rceil$, this probability is at most $\delta$ and
$b\le\beta\le88b$. The resulting upper coefficients are $750000$ for the
entropy--tail functional and $2670000$ for the critical rate. The
[complete statements and native audit](../results/known-law-confidence-20261104/README.md)
include both budget models. [Manuscript Appendix S](../paper/v6/appendix-known-confidence.tex)
