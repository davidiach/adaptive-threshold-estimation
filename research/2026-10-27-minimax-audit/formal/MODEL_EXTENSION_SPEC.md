# New specification: countably fresh coins and terminal tests

Status before proof: CONJECTURE (paper targets below). No Lean target is claimed.
This specification is separate from every historical freeze and does not change
the meaning of the Tier 3 or Tier 4 targets.

## Target N: failure of one-law termination transfer

For iid observed bits with parameter p, let X_n=2 bit_n-1 and
T=inf{n>=1: sum_{i<=n} X_i=1}, with inf(empty)=infinity.
Each bit is the first observation of a new coin with D=1/2 and constant sign
prior p. Then E_{5/8} T=4, P_{5/8}(T<infinity)=1, and
P_{3/8}(T<infinity)=3/5. This disproves the extension of Tier 3's
one-law-finite-work implies two-law-stopping conclusion to infinitely many iid
fresh coins, even for fixed gaps. It does not disprove its finite-family theorem.

## Target B: a conditional finite-prefix testing bridge

Let P and Q be probability laws of the same measurable observable-history policy,
with stopping time T, increasing prefix sigma fields F_n and independent seed
included. Suppose for every n the finite-prefix laws have KL at most
k E_P[min(T,n)], for a fixed k>=0. Suppose T is finite almost surely under both
laws and a terminal test phi is measurable at T, with
P(phi=1)>=1-delta and Q(phi=1)<=delta, 0<delta<1/2. If E_P T<=B<infinity,
then kl(1-delta,delta)<=kB. A sufficient way to ensure the required termination
is separate finite-work bounds under P and Q. The prefix bound is a hypothesis,
not a conclusion asserted for all channels.

## Observation semantics

The reservoir consists of independent latent draws (D_i,S_i) and independent
conditional observation tapes, with unknown q and known mu,rho as applicable.
Only observations and identities are visible. Countably many labels are allowed;
unobserved draws may be deferred. Each finite prefix observes at most n coins.
Deterministic computation and randomization are free but each action completes
after finite computation; infinitely many free operations cannot reveal a limit.
The canonical numbering reduction retains each revisit and does not reveal D_i.

## Review obligations

Prove exact stopping probabilities and expectation, including the nontermination
mass. Prove the testing limit without assuming termination transfers. Explain
how canonical finite-prefix reduction handles random gaps and what remains
unformalized. Keep stochastic proofs distinct from exact finite-prefix arithmetic.
