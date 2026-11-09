# The variational modulus in closed form, and the critical window

This package holds the numerical check for §14.8 of the
[consolidated v6 paper](../../paper/v6/README.md), whose source is
[psi-window.tex](../../paper/v6/psi-window.tex). The proofs are in the paper.

## Statements

Write $\mathcal Q^0$ for the closed quantile functional with the cost entropy
$\Gamma_\kappa$ of the quantile core replaced by its inverse-square cost
$A_\kappa$, and $E_\kappa$ for the entropy of the core's normalized band
costs, so that $\Gamma_\kappa=A_\kappa(1+E_\kappa)$. For every probability
law on $(0,1/2]$, $0<\rho\le1/4$ and $B>0$, with $h=B^{-1/2}$:

1. **$\Psi$ in closed form.**
   $\mathcal Q^0/\sqrt2\le\Psi_{\mu,\rho}(h)\le\mathcal K^0\le\mathcal Q^0$,
   where $\mathcal K^0$ is the selection functional with $\Gamma_\sigma$
   replaced by $A_\sigma$. Both outer constants are attained.
2. **The $\Psi$ lower bound as a corollary.** $\Psi\le\mathcal K\le\mathcal Q$,
   so the entropy–tail lower bound and the known-law confidence lower bound
   give $R\ge10^{-17}\Psi(B^{-1/2})$ and
   $r_{\rm exp}\ge10^{-17}\Psi(\sqrt{\log(1/\delta)/B})$ for every $B>0$.
   This derivation does not use the Lee–Valiant input of Appendix A.
3. **Distance from the rate.**
   $\Psi\le\mathcal K\le\mathcal Q\le\sqrt{2(1+E_\kappa)}\,\Psi$, with a
   matching lower bound when the core term dominates and the cap is
   inactive.
4. **Power laws, uniformly in the exponent.** For $F(d)=(d/a)^\alpha$ with
   $0<\alpha\le4$, the core has $a^2A_\kappa=\Phi_\alpha(\rho)$ and
   $\tfrac12[1+\log N_\alpha(\rho)]\le1+E_\kappa\le3.83[1+\log N_\alpha(\rho)]$.
   This gives $\mathcal R_\alpha/\sqrt2\le\mathcal Q\le2\mathcal R_\alpha$ for
   an explicit $\mathcal R_\alpha$, hence the RMS rate and both confidence
   radii with constants independent of $\alpha$. For $3/2\le\alpha\le3$ the
   rate is $\min\{\rho,\ x\sqrt{\rho\,\Phi_\alpha(\rho)[1+\log N_\alpha(\rho)]}\}$.

## Verification status

These are paper proofs. They rest on Corollary 14.6 and Theorem S.6 of the
paper, which have Lean-checked counterparts in the scopes recorded in §18,
and on elementary inequalities that are not formalized. Formalizing
$\Psi\le\mathcal K$ would let the existing Lean entropy–tail lower bound
imply the arbitrary-law $\Psi$ lower bound.

## Numerical check

```sh
python research/2026-11-09-psi-closed-form/check.py
```

[check.py](check.py) uses the standard library, floating-point arithmetic and
a fixed seed, and runs in a few seconds. It tests every inequality and
constant above on 4000 random finite laws, where $\mathcal K$ and
$\mathcal K^0$ are found by enumerating hard selections, and on a grid of
power laws whose core costs are evaluated band by band. It exits nonzero if
an inequality fails. A run at the commit that added this package printed:

```text
Part A: finite laws
  min Psi/Q0: 0.707110
  max Psi/Q0: 1.000000
  min K0/Psi: 1.000000
  max K0/Q0: 1.000000
  min K/K0: 1.000000
  max Q/K: 1.412618
  max Q/(sqrt(1+Ent) Q0): 1.000000
  max search/Psi: 1.000000
  min Q/(sqrt(1+Ent) Q0), core-dominated: 0.853803
Part B: power laws
  min a^2 Gamma/[Phi(1+log N)]: 0.590616
  max a^2 Gamma/[Phi(1+log N)]: 2.609395
  min Q/R_formula: 0.887041
  max Q/R_formula: 1.615042
  max T/(x sqrt(rho Phi)), window: 2.847127
  min R_formula/min(rho,Y), window: 1.000000
  max R_formula/min(rho,Y), window: 3.188061
  min Y/[x rho^e sqrt((1+log(1/eps))/eps)], u>=1: 0.973746
  max Y/[x rho^e sqrt((1+log(1/eps))/eps)], u>=1: 1.732051
All checks passed.
```

This is numerical evidence for the constants and the case analysis. It is
not a proof, and it does not test the statistical theorems that the
corollaries cite.
