# Track D: source check, upper-bracket diagnostics, and adaptation limits

## Published input audit

**Status: primary-source comparison; no Lean verification.**

Checked [Lee–Valiant, arXiv:1904.09228v3](https://arxiv.org/html/1904.09228v3),
Definition 14, Corollary 19, and its reduction to Proposition 20.
Definition 14 uses the note's normalization, H² = 1 − affinity.
Corollary 19 requires the prior, its increment, the gap, and the relative
increment all to be below a universal constant. It bounds H² divided by
expected work under both the original prior and the midpoint prior.
The note uses the original-prior version correctly. Choosing its constants
small enough also ensures that the absolute increment is small.

The source theorem covers sufficiently small gaps. The note explicitly extends
to gaps bounded away from zero by revealing the sign at the first requested
observation; that extension is its own data-processing argument, not a quotation
of the corollary. Parameter-independent randomization follows by conditioning
and averaging. Unbounded stopping follows by finite prefixes and convergence.
No discrepancy requiring a mathematical change was found. The original note
is preserved; no claim of independently re-proving the imported theorem is made.

## Power margins at and above two

**Status: proved on paper for the following integration identities; numerical
evidence for the evaluated upper bracket. No matching minimax upper theorem.**

Let D/a have density αu^(α−1) on (0,1), and x = na² ≥ 1. Integrating the
supplied classifier envelopes gives

\[
e_n=\mathbb E\min\{1,(nD^2)^{-2}\}
=\begin{cases}
\dfrac{4x^{-\alpha/2}-\alpha x^{-2}}{4-\alpha},&\alpha\ne4,\\
x^{-2}(1+2\log x),&\alpha=4.
\end{cases}
\]

Writing m_n = E min{n, [1+log₊(nD²)]/D²}, at α=2,

\[
a^2m_n=1+\log x+\tfrac12(\log x)^2.
\]

For α>2, let β=α−2 and q=x^(−β/2). Then

\[
a^2m_n=q+\alpha\left[\frac{1+\log x-q}{\beta}
-\frac{2(1-q)}{\beta^2}\right].
\]

**Proof.** Split each expectation at u=x^(−1/2). The first parts are
x^(−α/2) and x^(1−α/2), respectively. The tails are
αx^(−2)∫u^(α−5)du and α∫u^(α−3)[1+log x+2log u]du over
[x^(−1/2),1]. Integrating powers, and logarithms at the critical exponents,
gives the formulas. For x≤1 the values are e_n=1 and a²m_n=x.

`python tools/check_power_bracket.py` checks these identities by quadrature,
then optimizes the supplied note's certified finite-grid upper bracket over
all dyadic starting levels. It uses the original factors 17 and 34. Its results
are `results/power_bracket.json`; no sampling or random seed is involved.
The finite comparison does not settle the conjectured matching upper bound.
The logarithmic growth of m_n is a concrete obstacle for this classifier
envelope, rather than a proof that a better estimator is impossible.

## An obstruction to completely uniform adaptation to unknown rarity

**Status: proved on paper below; not Lean-checked.**

Fix a finite budget B, a known gap 0<d<1/2, and a single estimator A_B that
does not receive a rarity bound ρ. Assume it stops almost surely for every
constant positive-sign prior θ∈[0,1/4]. Include all independent algorithmic
randomness in the transcript. Even allowing observation interleaving and
adaptive coin creation, there is no such family with one universal finite C
satisfying, simultaneously for every B and ρ∈(0,1/4],

\[
\sup_{0\le\theta\le\rho}
\left(\mathbb E_\theta(\widehat\theta_B-\theta)^2\right)^{1/2}
\le C\min\left\{\rho,\frac{\sqrt\rho}{d\sqrt B}\right\}.
\]

**Proof.** For fixed B, put θ=0 and let ρ decrease to zero. Because the same
estimator is used for every ρ, its second moment under θ=0 is zero. It therefore
returns zero almost surely under θ=0.

For every finite stopped binary observation transcript, its conditional
probability given the random seed is strictly positive under θ=0 and every
θ∈[0,1/4]: both coin biases 1/2±d are strictly between zero and one. The action
and stopping rules are the same in all worlds. On the event T=t, mutual
absolute continuity follows from the finite observation likelihood ratio;
take the countable union over finite t. Almost-sure stopping makes this union
have full probability in every world. Thus the full stopped-transcript laws
are mutually absolutely continuous, including for continuously distributed
random seeds by conditioning. Zero output under θ=0 implies zero output under
every θ. At θ=ρ=1/4 its RMS error is 1/4, which contradicts the displayed bound
once B>4C²/d². This proves the assertion. Expected-work bounds imply the
almost-sure stopping premise, so they cannot circumvent it. ∎

This rules out this exact, fully uniform unknown-ρ formulation already for a
known fixed gap. It does not rule out adaptation with an additive error floor,
a known positive lower bound on ρ, a restricted budget/rarity range, or a
guarantee only for a supplied ρ. Distribution-blind adaptation with known ρ
remains a separate question. Two-success calibration controls work; alone it
cannot eliminate this statistical obstruction. No novelty claim is made.
