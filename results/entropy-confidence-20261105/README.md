# The sharper general-law confidence coefficient

This record verifies the explicit general-law confidence lower
coefficient $10^{-17}$ for the original observable adaptive experiment.

The proof checkpoint is
`0feee44f1e6dbdee6e3d8edb6c11eec2bc39ed60`.
It extends the additive-confidence publication checkpoint
`0ed90f918b7de70a06912c2b86d0043681316fc2`.

## Checked conclusion

For every known positive-gap probability law, $0<\rho\le1/4$,
$B>0$ and $0<\delta\le1/4$, put $\beta=B/\log(1/\delta)$.
Then

\[
10^{-17}Q(\beta)\le r_{\rm exp}(B,\delta)
\le r_{\rm hard}(B,\delta)\le750000\,\mathcal K(\beta).
\]

The lower coefficient also applies to the entropy–tail functional
because $\mathcal K\le Q$. The audit includes a lower bound for each
observable estimator satisfying the uniform expected-work and
failure guarantees.

## Direct comparison

The retained-entropy certificate bound holds at every positive cap.
Taking the exact cap-program infimum gives
$M\le16\cdot10^{14}P_\infty(b)$.
The remaining cutoff cases satisfy the same bound, and the tail
modulus satisfies $T\le32P_\infty(b)$. Consequently

\[
30\cdot10^{-17}Q(b)\le P_\infty(b).
\]

The existing stopped confidence lower bound
$P_\infty(\beta)/30$ completes the stronger coefficient.

The [proof map](../../docs/ENTROPY_CONFIDENCE.md) describes the
three new modules. The [full theorem](../../lean/ThresholdHC/ConfidenceEntropy/Full.lean)
combines the lower comparison with the existing hard-cap construction.

## Native evidence

- Six exact statements and six transitive axiom reports.
- 629 project modules in the dependency closure.
- Three new modules compiled with empty diagnostic logs.
- Ten unchanged inherited genie modules recompiled from source.
- 616 further inherited objects matched to their published hashes.
- Source, direct-dependency object and output-object identities checked together.
- Only `propext`, `Classical.choice` and `Quot.sound` appear in the reports.
- The source guard checked all 983 Lean files.
- The frozen-source guard, 15 verifier regression tests and 12 manuscript regression tests passed.

Three inherited files retain reviewed style diagnostics.
`Genie/LatentModel.lean` suggests simpler tactic sequencing and a local
instance declaration.
`Genie/FinitePosterior.lean` suggests the same local-instance style.
`Genie/OptimizedConvergence.lean` identifies an implicitly used binder.
Their exact diagnostic hashes are recorded, and their logs remain
part of the evidence. The inherited sources are unchanged.

The [status record](status.json) identifies the compiler and full
source/object closure. The [exact audit input](confidence_entropy.lean)
and [native log](confidence_entropy.log) record the six checks.
The numbered logs follow the fresh compilation order in the status
file.

## Manuscript

The [161-page manuscript](../../paper/v6/builds/entropy-confidence-20261105.pdf)
updates the main confidence theorem and adds the direct comparison
proof. Its [build record](../../paper/v6/builds/entropy-confidence-20261105.json)
records two byte-identical offline builds, all six changed pages
visually inspected, 368 labels and 29 citations. There are no new
layout defects. Earlier manuscripts and evidence remain preserved.

## Remaining scope

The sharp quantile-factor characterization retains its paper proof.
Law-dependent time-uniform lower bounds, unknown-law oracle-rate
adaptation, unrestricted selection complexity and the optimal cap
convergence rate remain open research. Human specialist review
remains absent.
