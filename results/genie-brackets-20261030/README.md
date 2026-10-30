# Monotone genie brackets and Bellman certificates

This additive checkpoint follows `024bc0f` on the branch based at `8fc36ac`.
Protected sources and all commands appear in `status.json`; `ExactAudit.lean`
checks eight independently stated theorem types.

The latent-reveal program uses the original charged stopping-flow cone and
work reference, substituting the latent-reveal reward only at the terminal
layer. For every positive cap,

    K_N <= K_infinity <= K_N^+,   K_(N+1)^+ <= K_N^+.

These comparisons retain extended values and require no finite-divergence
assumption. Ordinary prefix information is bounded by the reveal reward,
whose two child rewards sum exactly to the parent reward. Truncating a
later flow reduces paid work and increases its reveal information. The
proof uses additive extended-real conservation, without subtracting infinity.

For finite latent divergence C_v, the exact residual formula gives

    K_N^+ - K_N <= e_N,   e_N = C_v - terminalInformation_N.

The genie ratio is attained by a deterministic Bellman count policy. For a
nonnegative finite price, the modified Bellman root is nonpositive exactly
when that price bounds the genie ratio. A full-depth reveal has information
C_v, so for every positive cap K_N^+ is infinite iff C_v is infinite.

This checkpoint does NOT yet prove e_N -> 0, optimized genie convergence,
the finite-support genie SOCP, or the separate entropy-tail statistical
lower bound. Those are distinct claims; finite-cap error control alone is
not a convergence proof.

The audit rebuilt nine new modules and checked 101 declarations in twelve
modules, eight exact types and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Other dependencies used cached objects
with recorded source hashes. This was not a full dependency rebuild or CI
run. All four verifier regression tests passed.

Reproduce with `python tools/verify_genie_brackets.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Use fresh `.runtime`
output. Logs 001 through 009 are source builds; 010 is the exact-type and
transitive-axiom audit.
