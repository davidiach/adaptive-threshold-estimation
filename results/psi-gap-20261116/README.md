# The distance of Ψ from the rate

For a probability law $\mu$ on $(0,1/2]$, $0<\rho\le1/4$ and $B>0$, put
$h=B^{-1/2}$ and let $\mu=\nu+\kappa$ be the quantile split at the threshold
$t$, with its fractional boundary atom. Write $a_j(\kappa)$ for the
inverse-square cost of $\kappa$ on the dyadic band $I_j$,
$A_\kappa=\int d^{-2}\,d\kappa$ for the total, and

$$E_\kappa=\sum_j-\frac{a_j(\kappa)}{A_\kappa}\log\frac{a_j(\kappa)}{A_\kappa}$$

for the entropy of the normalized band costs. $\Psi$, $\mathcal K$,
$\mathcal Q$ and $\mathcal Q^0$ are as in the
[closed-form record](../psi-closed-form-20261116/README.md), and $R$ is the
minimax RMS risk of the original observable experiment: budgets count actual
flips, rarity is the global bound $\int q\,d\mu\le\rho$, and magnitudes and
signs stay hidden. This is Theorem 14.11 of
[v6 §14.8](../../paper/v6/psi-window.tex).

| Statement | Lean-checked guarantee |
|---|---|
| [Core entropy](../../lean/ThresholdHC/PsiGap/Entropy.lean) | $0<A_\kappa<\infty$, $E_\kappa\ge0$, $\Gamma_\kappa=A_\kappa(1+E_\kappa)$ and $E_\kappa\le\log\log_2(1/t)$. |
| [Chain (W4)](../../lean/ThresholdHC/PsiGap/Full.lean) | $\Psi(h)\le\mathcal K\le\mathcal Q\le\sqrt{1+E_\kappa}\,\mathcal Q^0$ and $\mathcal Q\le\sqrt{2(1+E_\kappa)}\,\Psi(h)$. |
| [Risk](../../lean/ThresholdHC/PsiGap/Full.lean) | $10^{-17}\,\Psi(h)\le R\le30001\sqrt{2(1+E_\kappa)}\,\Psi(h)$. |
| [Reverse bound](../../lean/ThresholdHC/PsiGap/Full.lean) | If $T_h\le h\sqrt{\rho A_\kappa}$ and $T_h+h\sqrt{\rho\Gamma_\kappa}\le\rho$, then $\mathcal Q\ge\tfrac12\sqrt{1+E_\kappa}\,\mathcal Q^0$ and $R\ge\tfrac12\,10^{-17}\sqrt{1+E_\kappa}\,\Psi(h)$. |

Every statement holds for every probability law on $(0,1/2]$, every
$0<\rho\le1/4$ and every $B>0$.

## Where the Lean statements differ from the paper

- **Upper coefficient.** The risk bound uses the checked
  $R\le30001\,\mathcal Q$. The paper's display has its own constant 33000.
- **Reverse risk coefficient.** Lean has $10^{-17}\mathcal Q\le R$ directly,
  so the reverse risk bound has coefficient $\tfrac12\,10^{-17}$, without the
  factor $1/(1+2\sqrt2)$ of the paper's display.
- **Entropy bound.** The paper states
  $E_\kappa\le\log n_\kappa\le\log\log_2(1/t)$, with $n_\kappa$ the number of
  bands that $\kappa$ occupies. Lean states only the outer bound. Its proof
  compares with the uniform law on the $N$ bands that meet $[t,1/2]$, where
  $N\le\log_2(1/t)$; the bound by $n_\kappa$ is not stated.
- **Hypotheses of the reverse bound.** They are stated in the extended
  nonnegative reals, with the tail cost $T_h$ of the specification.

## What is not checked

The two-atom sharpness example of Proposition 14.9, Lemma 14.12,
Theorem 14.13 and Corollary 14.14. The `psi-closed-form` entry of
[status.json](../../paper/v6/status.json) names them, so it stays a
paper-proof entry. No manuscript source and no PDF changes with this record.

## Proof

A finite measure on $d\ge t$ has no mass on the bands $I_j$ with
$b_j<t$, so only $I_0,\dots,I_{N-1}$ carry cost, and $t\le b_{N-1}=2^{-N}$
gives $N\le\log_2(1/t)$. The cost entropy is a supremum over prefixes of the
band costs, which is attained at the prefix of length $N$; the band costs sum
to $A_\kappa$ because the bands are disjoint and cover the support. The
checked normalization of the homogeneous entropy gives
$\Gamma_\kappa=A_\kappa(1+E_\kappa)$, and the checked cross-entropy bound
against the uniform law on $N$ bands gives $E_\kappa\le\log N$.

The core term of $\mathcal Q$ is then $\sqrt{1+E_\kappa}$ times the core term
of $\mathcal Q^0$, and $\min\{\rho,sx\}\le s\min\{\rho,x\}$ for $s\ge1$. The
rest composes the checked [closed form](../psi-closed-form-20261116/README.md)
$\mathcal Q^0\le\sqrt2\,\Psi$ and $\Psi\le\mathcal Q^0$, the checked
[comparison](../psi-selection-20261109/README.md) $\Psi\le\mathcal K$, and the
checked bounds $10^{-17}\mathcal Q\le R\le30001\,\mathcal Q$.

## Evidence

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/bea093c)
every project module was built from source on Linux with Lean `v4.36.0-rc1`
and the Mathlib cache for the pinned revision; the
[native record](status.json) lists the source hashes. The three new modules
compiled without warnings. [Eight exact statements](psi_gap.lean) passed with
[18 transitive axiom reports](psi_gap.log), every declaration in the
directory included, using only `propext`, `Classical.choice` and
`Quot.sound`. The four restatements write out $A_\kappa$, $E_\kappa$ and
$\mathcal Q^0$ instead of naming them. Run `python tools/verify_psi_gap.py`
with the pinned toolchain.

On the same checkout `python tools/verify_project_axioms.py` verified 13,072
constants (10,574 theorems) in 1,220 modules, 125 exported instances and 2,387
definition fingerprints. Fourteen fingerprints are new: eight from
`PsiClosedForm/` and six from `PsiGap/`; no existing entry changed. The kernel
replay was not run locally.

The specification was written together with the proof; its hash is pinned in
the verifier from this checkpoint on. The commit message of the checkpoint
says the audit had not yet run; it was run afterwards on unchanged sources.
This is a local record, not a CI result, and it has had no independent review.
