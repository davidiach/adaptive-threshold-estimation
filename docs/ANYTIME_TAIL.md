# Infinite-moment tail families

This development supplies the infinite-moment construction for
[observable sequential testing](ANYTIME_SEQUENTIAL.md). The comparison with
the final iterated-logarithm selection rate is a separate asymptotic step.

For a positive-gap law with nonintegrable inverse gap and any positive rarity
ρ, dominated convergence supplies 0<τ≤1/4 with

    0 < μ{d≤τ} ≤ ρ/2.

Set ε_j=τ4^(−j), g_j(d)=min(1,ε_j/d) on {d≤τ}, and g_j(d)=0 elsewhere.
The masses W_j=∫g_j are positive, antitone and tend to zero. Also
W_(j+1)≥W_j/4. Starting at j_0=0, choose the first later index j_(k+1) with
W_(j_(k+1))≤W_(j_k)/4. Minimality gives a plateau before that index and
W_(j_(k+1))>W_(j_k)/16.

Use one reference prior q_0=1/4 on {d≤τ}, zero elsewhere. At step k use

    q_k = q_0 + (g_(j_k) − g_(j_(k+1)))/32.

All these are measurable sign priors, rare under the original integral
constraint, and lie in [1/4,9/32] on the small-gap region. Their mean increments
a_k are positive and satisfy

    a_k = (W_(j_k) − W_(j_(k+1)))/32 ≥ 3W_(j_k)/128,
    3a_k ≤ a_i  for i<k,
    d |q_k(d)−q_0(d)| ≤ ε_(j_k)/32.

The finite-transcript proof handles early stopping, adaptive creation labels,
revisits of the same latent sign, and deterministic observations where the
priors agree. Central posterior bounds control each differing observation.
Integration over the seed and hidden iid gap array, followed by data processing
that forgets the gaps, proves

    KL(observablePrefixLaw(q_k,n) || observablePrefixLaw(q_0,n))
      ≤ n ε_(j_k)^2.

For any positive antitone information scale s_k, define the integer budget

    n_k = floor(((1−δ)/2) log(k+2) / s_k²).

The schedule is monotone and unbounded. Its testing terms dominate
exp(−log(k+2)/2), so they are not summable. Taking s_k=ε_(j_k), the first-crossing
theorem forces

    t(n_k) ≥ W_(j_k)/256

infinitely often. The final infiniteMoment_unbounded statement supplies the
small-gap region and these violations beyond every prescribed physical budget
for every law with nonintegrable inverse gap.

This is a construction and testing theorem in the actual observable experiment.
It does not by itself prove the final comparison to
K(n/[log(1/δ)+log log n]). The dense and sparse block comparisons and finite
asymptotic coefficient case are further proof obligations.

Run python tools/verify_anytime_tail.py for the exact-statement and transitive
axiom audit. Earlier finite rational profile regressions remain historical
evidence for their own construction.

The [native audit record](../results/anytime-tail-20261105/README.md) binds fifteen exact statements to the proof commit, compiler inputs, axiom reports and dependency hashes.
