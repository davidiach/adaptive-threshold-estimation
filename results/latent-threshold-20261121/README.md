# Threshold form of the target: library audit

The paper writes the target as $\theta(G)=P_G(P>1/2)$, the probability that a
coin's success probability exceeds one half. Lean defines the target as
$\theta=\int q\,d\mu$ and the latent parameter law $G_{\mu,q}$ of the
independent-tape construction, but proved $\theta=G_{\mu,q}(P>1/2)$ only for
laws with a density
([`represents_threshold_mean`](../../lean/ThresholdHC/SmoothDensity/LatentLaw.lean));
the [model-fidelity brief](../../docs/MODEL_FIDELITY.md) recorded the general
case as not stated. Lean now states it for every law, in
[`lean/ThresholdHC/LatentThreshold`](../../lean/ThresholdHC/LatentThreshold/Full.lean).
The audit runs below were made at commit
[`703d353`](https://github.com/davidiach/adaptive-threshold-estimation/commit/703d353).

## Statement

[`Specification.lean`](../../lean/ThresholdHC/LatentThreshold/Specification.lean)
states one target, `threshold_mean`: for every probability law $\mu$ of gaps
and every measurable sign law $q$,
$$\int q\,d\mu=G_{\mu,q}\bigl(\{p:p>1/2\}\bigr),$$
where $G_{\mu,q}$ (`SmoothDensity.latentLaw`) is the law of $1/2+d$ with
probability $q(d)$ and $1/2-d$ otherwise, $d\sim\mu$. It is the per-coin
parameter law of the original experiment.

## How the proof goes

The proof is in [`Threshold.lean`](../../lean/ThresholdHC/LatentThreshold/Threshold.lean).
The latent law integrates a bounded measurable $F$ to
$\int[q(d)F(1/2+d)+(1-q(d))F(1/2-d)]\,\mu(dd)$
([`populationParameterLaw_integral`](../../lean/ThresholdHC/CriticalEntropy/PopulationTapeLaw.lean)).
For the indicator of $\{p>1/2\}$ the integrand is $q(d)$, because
$1/2+d>1/2\ge1/2-d$ for every gap $d>0$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_latent_threshold.py --replay --jobs 3` | 2 exact statements (the target and one component, with the latent law written out) and 4 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [latent-threshold-audit.log](latent-threshold-audit.log) |
| `python -m unittest discover -s tools -p 'test_latent_threshold.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,098 constants (13,731 theorems) in 1,469 modules, same axioms. 147 exported instances. 3,227 locked definition fingerprints. | [project-audit.log](../stopped-time-uniform-20261121/project-audit.log) of the stopped time-uniform record, the same run |
| `python tools/verify_lean_sources.py` | 1,470 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added seven
entries to `tools/definition_lock.json`: the three statements of
`StoppedTimeUniform`, the statement of `LatentThreshold`, the two statements of
`ZeroAtomSplit` and the statement of `CapIdentificationEstimate`. No existing
entry changed. The run recorded here is a later one without that flag; it
covers all four groups.

## Scope

This audit checks that the stated type is proved and which axioms the proof
uses. The specification was written after the proof; it is pinned by hash
from this audit onward. The converse, that every law $G$ of the success
probability with no atom at $1/2$ is some $G_{\mu,q}$, needs a measurable
disintegration by $|P-1/2|$ and is not formalized; the paper treats it as a
standard step.

## Review

Before the specification was pinned, a reviewer that had not written the proof
checked that `latentLaw` is the per-coin parameter law of the original
experiment, that the event $p>1/2$ is the positive sign because gaps are
positive, and that the proof is sound. It found no blocking problem; its
wording fixes were applied, and the component is now restated with the latent
law written out. This was a review by an AI agent, not a specialist referee
report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
