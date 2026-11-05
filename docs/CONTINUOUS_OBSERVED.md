# Continuous-magnitude observed-state lower bounds

The continuous-magnitude lower bounds are Lean-checked for deterministic
conditional Bernoulli models on a uniform observed state space. Their
gap law is exactly uniform on \((0,1/4]\). Query policies may choose any
point, revisit states, interleave cells and use unbounded stopping.

For sufficiently small positive \(\varepsilon\), the expected-work
lower coefficient on \(\varepsilon^{-2}\log^2(1/\varepsilon)\) is
\[
 c=\frac{225\,\operatorname{kl}(7/8,1/8)}{128\cdot64^2}>0
\]
at failure probability \(1/16\). The RMS coefficient is \(c/64\).
The class includes arbitrarily fine finite measurable sign-cell
partitions and is fixed before the requested accuracy.

## Physical experiment

A query of gap \(d\) in a cell with cap \(b\ge d\) uses one raw cell
observation followed by independent sign-symmetric noise of probability
\((1-d/b)/2\). The checked history decoder preserves the stopping pattern
and actual observation count. It uses only preceding transformed outcomes.

The simulation retains the original private seed jointly with the
observations. Its finite prefixes follow the ordinary fresh Bernoulli
rule at every selected state. Those prefix laws uniquely determine the
complete transcript measure. Estimation error and expected work transfer
exactly, so the lower bound applies to every physical experiment with
that observation rule.

The finite-cell construction keeps the underlying gap coordinate
unrounded. Capping gaps and cell magnitudes at one quarter preserves
the exact gap law, target separation and concentration condition.
The bound holds at every state, including states of probability zero.

## Density and conditional moments

The audit identifies the actual conditional mean, threshold target and
gap magnitude. The conditional variance is at least \(3/4\), and the
centered observation is bounded by \(3/2\).

The normalized conditional magnitude has density
\[
 \frac{2\,\mathbf1_{(0,Z(1/4)]}(z)}
 {(1+z^2)\sqrt{1+z^2}},\qquad
 Z(d)=\frac{2d}{\sqrt{1-4d^2}},
\]
bounded globally by two. A checked monotone change of variables
establishes the density identity. Every normalized conditional central
moment of real order \(q\ge0\) is bounded by \(3^{q/2}\).

These bounds verify the density and moment requirements in Assumptions
2.1 and 2.4 of the authors' paper. [Giles–Haji-Ali](https://arxiv.org/pdf/1802.05016)

## Proof map and audit

- Decode, Tape, Prefix and Word implement the causal observation transform.
- Noise, UniformTape and FreshObservation identify each transformed observation and its independent unused randomness.
- Reduction, PrefixLaw, QueryPrefix and QueryLower connect the complete physical experiment to the finite-cell testing bound.
- Cutoff, UniformGaps and UniformReal construct the exact uniform law with pointwise bounds.
- BinaryMoments, Normalization, NormalizationGeometry, Density and Regularity establish the actual density and conditional-moment identities.
- Scale, UniformLower and UniformRMSLower prove the two complexity lower bounds.

Run `python tools/verify_continuous_observed.py` for 34 exact statements and 87 transitive axiom reports.
The construction uses the second-moment replication count from the
[finite-cell theorem](OBSERVED_STATES.md).

## Remaining upper-bound transfer

The matching upper rate retains its paper proof. Its formal continuation
constructs a selected-state policy from the existing population estimator
using independent uniform outer states, then identifies their complete
observation laws and transfers actual work and risk.
