# Uniform convergence of the finite-cap stopping programs

The [Lean theorem](../../lean/ThresholdHC/GenieRate/Full.lean) compares the
original finite ordinary value $P_N$ and the optimized latent-reveal value
$G_N$. For every positive-gap law, $0<\rho\le1/2$, $B>0$ and $k>1$,
$$
 N(1-1/k)^2(k^2-1)\ge B \quad\Longrightarrow\quad P_N\le kG_N .
$$
At $N\ge4B/3$, this gives $P_N\le2G_N$ and $R\le P_N\le16R$. It also
checks the rate $P_N\le(1+2t)G_N$ when $0<t\le1$ and $B\le Nt^3$.
These are statements about the optimized programs. The proof mixes both
references with the midpoint and charges every branch that reaches the cap
for all $N$ observations. [Mathematical derivation](../../docs/FINITE_CAP_RATE.md)

The [native record](status.json) lists the 395 project modules in the
dependency closure. It checks 309 inherited object hashes against an
earlier record. Another 83 objects come from the [published native
build](../rare-event-full-20261031/status.json). Their source hashes and
successful compiler commands are checked against that record. Their object
hashes were first recorded in this audit. Three new modules were compiled.
The [audit source](ExactAudit.lean) and [compiler output](04.log) give
three expanded statement checks and ten transitive axiom reports using only
propext, Classical.choice and Quot.sound.

Run `python tools/verify_genie_rate.py` from the repository root. The
separate `python tools/verify_finite_cap_rate.py` replay uses exact rationals
and the existing Bellman solver with 576 finite examples, including 112
quartet/cap inputs with infinite unregularized latent divergence.
