# The closed form of Ψ within a factor √2

For a probability law $\mu$ on $(0,1/2]$, $0<\rho\le1/4$ and $B>0$, put
$h=B^{-1/2}$. Write $\Psi_{\mu,\rho}$ for the variational modulus,
$\mathcal K$ for the entropy-tail selection functional and $\mathcal Q$ for
the closed quantile functional, as in the
[results guide](../../docs/RESULTS.md#the-variational-modulus-in-closed-form).
Let $\mu=\nu+\kappa$ be the quantile split, with its fractional boundary atom,
and $A_\sigma=\int d^{-2}\,d\sigma$. The entropy-free functionals of display
(W1) of [v6 §14.8](../../paper/v6/psi-window.tex) are

$$\mathcal Q^0=\min\{\rho,\ T_h+h\sqrt{\rho A_\kappa}\},\qquad
\mathcal K^0=\min\Bigl\{\rho,\ \inf_{\sigma\le\mu}\Bigl[h\sqrt{\rho A_\sigma}+\int\min\{1,h/d\}\,d(\mu-\sigma)\Bigr]\Bigr\},$$

with $T_h=\int\min\{1,h/d\}\,d\nu$. All statements are deterministic: no
experiment and no estimator occurs in them.

| Statement | Lean-checked guarantee |
|---|---|
| [Order of the functionals](../../lean/ThresholdHC/PsiClosedForm/Order.lean) | $\mathcal K^0\le\mathcal K$, $\mathcal Q^0\le\mathcal Q$ and $\mathcal K^0\le\mathcal Q^0$. |
| [Closed form](../../lean/ThresholdHC/PsiClosedForm/Full.lean), display (W2) | $\mathcal Q^0\le\sqrt2\,\Psi_{\mu,\rho}(h)$ and $\Psi_{\mu,\rho}(h)\le\mathcal K^0\le\mathcal Q^0$. |
| [Trivial regime](../../lean/ThresholdHC/PsiClosedForm/Full.lean) | If the quantile threshold $t$ satisfies $t\le h$, then $\Psi_{\mu,\rho}(h)=\mathcal Q^0=\rho$. |

Every statement holds for every probability law on $(0,1/2]$, atoms and a
split boundary atom included, every $0<\rho\le1/4$ and every $B>0$.

## What is not checked

- The second sharpness statement of Proposition 14.9: the two-atom law for
  which $\Psi=\mathcal Q^0/\sqrt2$. That the factor $\sqrt2$ cannot be
  improved therefore remains a paper proof.
- Theorem 14.11 (the distance of $\Psi$ from the rate), Lemma 14.12 and
  Theorem 14.13 (power laws with constants uniform in the exponent), and
  Corollary 14.14.
- The `psi-closed-form` entry of [status.json](../../paper/v6/status.json)
  names all of these, so it stays a paper-proof entry. No manuscript source
  and no PDF changes with this record.

## Proof

The upper bound $\Psi\le\mathcal K^0$ is the argument of the checked
comparison $\Psi\le\mathcal K$, stopped before the inverse-square cost is
weakened to the cost entropy.

For the lower bound, let $c$ be the cutoff of the checked
[optimizer](../../lean/ThresholdHC/Tier3/Optimizer.lean), so that
$v=\min\{1,c^2/d^2\}$ has mass $\rho$, and put $a=\sqrt v$ and
$k=\min\{1,h/d\}$. The cutoff lies strictly below $t$, so $\kappa$ lives on
$d>c$. If $h\ge c$ the objective of $v$ is $\rho$. If $h<c$ its integrand is
$ak$, and with $w=\int v\,d\kappa$:

- on the core, $ak=(h/c)v$ and $d^{-2}=v/c^2$, so the core contributes
  $(h/c)w$ and $A_\kappa=w/c^2$;
- on the tail, $k\ge(h/c)a$ with equality where $a<1$, hence
  $k(1-\sqrt2a)\le(h/c)\,a(1-\sqrt2a)$ at every gap;
- the budget identity is $\int a^2\,d\nu+w=\rho$, and the Cauchy–Schwarz
  inequality on the tail, of mass $\rho$, gives
  $\int a\,d\nu\le\sqrt{\rho\int a^2\,d\nu}$.

Since $\sqrt{\rho x}+\sqrt{\rho(\rho-x)}\le\sqrt2\,\rho$, these give
$T_h+h\sqrt{\rho A_\kappa}\le\sqrt2\,V$ for the objective value $V$ of $v$.
The paper's proof uses the same allocation and splits the tail at $c$ into
five integrals; this arrangement does not need the split. The paper proof is
unchanged.

## Evidence

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/5ffc082bf8ef8201dde45601bc28b1af203c5b2c)
the four new modules and the project modules they import were built from
source on Linux with Lean `v4.36.0-rc1` and the Mathlib cache for the pinned
revision; the [native record](status.json) lists the source hashes. The new
modules compiled without warnings. [Six exact statements](psi_closed_form.lean)
passed with [36 transitive axiom reports](psi_closed_form.log), every
declaration in the directory included, using only `propext`,
`Classical.choice` and `Quot.sound`. The three restatements write out
$\mathcal K^0$ and $\mathcal Q^0$ instead of naming them. Run
`python tools/verify_psi_closed_form.py` with the pinned toolchain.

The specification was written together with the proof; its hash is pinned in
the verifier from this checkpoint on. This record is a local audit of the
import closure of the new modules. It is not a CI result, and it has had no
independent review.
