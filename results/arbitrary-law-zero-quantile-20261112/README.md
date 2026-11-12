# The quantile design with a zero atom

This record covers (A16) of the
[arbitrary-law adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator):
the quantile design of a reference law that has unresolved mass at zero, and
its comparison with the selection functional.

Let $\alpha=z\delta_0+(1-z)\eta$, where $\eta$ is a probability law of positive
gaps and $z$ is the mass at zero. Fix a rarity $\rho$ and a budget $B$, and
write $h=B^{-1/2}$. The design removes the lowest-gap mass $\rho$ of $\alpha$:
the zero atom, and the lowest-gap mass $\rho-z$ of the positive part. Under
$\eta$ that is the quantile part $\nu$ of mass $r=(\rho-z)/(1-z)$, with a
fraction of a boundary atom; $\sigma$ is the remaining quantile core. With the
tail modulus $\tau_\nu(h)=\int\min\{1,h/d\}\,d\nu$ and the cost entropy
$\Gamma_\sigma$,

$$
 Q_\alpha(B)=\min\{\rho,\;z+(1-z)\,\tau_\nu(h)+h\sqrt{\rho\,(1-z)\,\Gamma_\sigma}\}
 \quad(z<\rho),\qquad Q_\alpha(B)=\rho\quad(z\ge\rho).
$$

$K_\alpha(B)$ is the
[selection functional extended to laws with mass at zero](../../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroModel.lean),
with the infimum over all fractional selections, and $K_{\eta,r}$, $Q_{\eta,r}$
are the positive-gap functional and closed quantile value at rarity $r$. All
statements are in
[ZeroQuantile.lean](../../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroQuantile.lean).

| Statement | Lean-checked guarantee |
|---|---|
| (A16) | For every probability law $\alpha$ on $[0,1/2]$, every $0<\rho\le1/4$ and every $B>0$: $Q_\alpha(B)\le4K_\alpha(B)$. |
| Converse | For every such law, every $\rho\le1$ and every $B$: $K_\alpha(B)\le Q_\alpha(B)$. For $z<\rho$ the second term of $Q_\alpha$ is the selection objective of $\alpha$ at the admissible selection $(1-z)\sigma$. |
| Normalization | A probability law $\alpha$ on $[0,1/2]$ with $\alpha\{0\}<1$ equals $z\delta_0+(1-z)\eta$, with $z=\alpha\{0\}$ and $\eta$ its positive part divided by $1-z$, which is a probability law of positive gaps. |
| Zero floor | For a finite measure $\alpha$ on the real line, $\rho>0$ and $B>0$: $K_\alpha\ge\min\{\rho,\alpha\{0\}\}$. With the cap this gives $K_\alpha=\rho$ when $z\ge\rho$, and in the proof of (A16) it gives $Q_\alpha\le\rho\le2K_\alpha$ when $z\ge\rho/2$. |
| Scaling | $K_\alpha\ge(1-z)K_{\eta,r'}$ whenever $z<1$, $r'\ge0$ and $(1-z)r'\le\rho$. |
| Both cap cases | For $0\le z\le\rho/2$ and $0<\rho\le1$: $Q_\alpha\le z+\sqrt2\,(1-z)\,Q_{\eta,r}$. |
| No zero atom | For $z=0$ and $\rho>0$, $Q_\alpha$ is the closed quantile value of $\eta$. |

For $z<\rho/2$ the bound combines the last three rows with the existing
[8/5 comparison](../../lean/ThresholdHC/QuantileSelection/Full.lean)
$Q_{\eta,r}\le(8/5)K_{\eta,r}$: $Q_\alpha\le z+(8\sqrt2/5)(1-z)K_{\eta,r}\le(1+8\sqrt2/5)K_\alpha$,
and $1+8\sqrt2/5<4$. The parametrized statements hold for every probability
law $\eta$ of positive gaps and every $z\ge0$.

The design matches the split that the
[toolkit's envelope oracle](../../toolkit/threshold_toolkit/gap_envelope.py)
hands to the planner: the positive conditional law at the conditional rarity
$r$, with its integrals scaled by $1-z$ and the zero atom added to the
unresolved mass. That correspondence is by inspection and is not Lean-checked.

This is the comparison (A16) only. It does not include:

- The planner itself: its cap search, multilevel allocation, integral
  enclosures and work and error certificate, and their connection to the
  Lean-checked level certificates.
- The planned RMS coefficient $C_0$, the reported radius coefficient $C_*$
  and the relative square-root enclosure.
- The robust continuation, the all-budget controller and the arbitrary-law
  adaptation theorem, which remains a paper proof.
- Python execution of the toolkit.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/7bc6d60c1ac8022faa7d817c60d21ca79bd2e1e2),
the new module was built from source on Linux with Lean `v4.36.0-rc1`, on top
of a build of every project module made in the same environment and against
the Mathlib cache for the pinned revision. It compiled without warnings.
[22 exact statements](arbitrary_law_zero_quantile.lean) passed with
[22 transitive axiom reports](arbitrary_law_zero_quantile.log), one for each
declaration of the module, using only `propext`, `Classical.choice` and
`Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,172 modules, 12,366 constants and 9,984 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new module.

One check outside Lean was run during review and is supporting evidence only.
On 1,500 random finite laws with a zero atom, 764 of them with $z<\rho/2$, a
literal transcription of $Q_\alpha$ in floating point satisfied
$K_\alpha\le Q_\alpha\le4K_\alpha$, and the largest ratio $Q_\alpha/K_\alpha$
was 1.39. There $K_\alpha$ came from the
[toolkit's exhaustive enclosure](../../toolkit/threshold_toolkit/rare_event_functional.py)
of the positive-gap functional through
$K_\alpha=\min\{\rho,z+(1-z)K_{\eta,\rho/(1-z)}\}$, an identity that is not
Lean-checked.

Run `python tools/verify_arbitrary_law_zero_quantile.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the module is not registered.
