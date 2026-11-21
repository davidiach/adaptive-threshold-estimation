# The population class and the G-form of the target: library audit

The model section of the v6 manuscript
([`paper/v6/core.tex`](../../paper/v6/core.tex), `sec:model`, equation
`eq:model`) defines a population by $D\sim\mu$, $S\mid D=d\sim\mathrm{Ber}(q(d))$
and $P=\frac12+(2S-1)D$, with population class
$\mathcal G(\mu)=\{G_{\mu,q}:q\text{ measurable}\}$. The introduction
([`paper/v6/introduction.tex`](../../paper/v6/introduction.tex), `eq:target`
and `eq:modulus-intro`) writes the target as $\theta(G)=P_G(P>1/2)$ and $\mu$
as the law of $|P-1/2|$. Lean works with $(\mu,q)$. Since 21 November 2026
it states $\theta=G_{\mu,q}(P>1/2)$ for every gap law and sign law
([record](../latent-threshold-20261121/README.md)), but the converse, that
every law $G$ with $|P-1/2|\sim\mu$ is some $G_{\mu,q}$, was not formalized.
The model-fidelity brief asks a reviewer whether that is acceptable
([`docs/MODEL_FIDELITY.md`](../../docs/MODEL_FIDELITY.md), question 5). Lean
now checks it, in
[`lean/ThresholdHC/LatentDisintegration`](../../lean/ThresholdHC/LatentDisintegration/Full.lean).
The paper is unchanged. The audit runs below were made at commit
[`45e06a3`](https://github.com/davidiach/adaptive-threshold-estimation/commit/45e06a3).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/LatentDisintegration/Specification.lean)
uses `SmoothDensity.latentLaw μ q` for $G_{\mu,q}$, a law on $[0,1]$. The
magnitude law $|P-1/2|\sim\mu$ is read on $\mathbb R$: the law of $|P-1/2|$
under $G$ equals the law of the gap under $\mu$. This already rules out an
atom at $P=1/2$, since every gap is positive. The map `gapOf` reads $|P-1/2|$
as a gap; it sends the null point $P=1/2$ to the default $1/2$, and enters only
the component form of the converse.

| Target | Statement |
|---|---|
| `latent_magnitude` | Every $G_{\mu,q}$ has magnitude law $\mu$. |
| `latent_disintegration` | Every probability law $G$ of $P$ with $G\{P=1/2\}=0$ is $G_{\mu,q}$ for its magnitude law $\mu=\mathcal L(\mathrm{gapOf}\,P)$ and some sign law $q$. |
| `population_class` | For every probability gap law $\mu$, a law $G$ on $[0,1]$ is some $G_{\mu,q}$ if and only if $|P-1/2|\sim\mu$ under $G$. |
| `g_form_target` | If $|P-1/2|\sim\mu$ under $G$, then $G$ is some $G_{\mu,q}$, and every sign law $q$ with $G_{\mu,q}=G$ has $\theta=\int q\,d\mu=P_G(P>1/2)$. |

The paper gives no written proof of the converse. The sign law $q$ is unique
only $\mu$-almost everywhere; that uniqueness is not stated, and the target
statement covers every representing $q$, so $\theta(G)$ is well defined
without it. The risk theorems are not restated in $G$-form.

## How the proofs go

- [`Magnitude.lean`](../../lean/ThresholdHC/LatentDisintegration/Magnitude.lean):
  the gap map, its measurability and value off $1/2$, and the magnitude law of
  $G_{\mu,q}$ through the product structure of the latent law.
- [`Disintegration.lean`](../../lean/ThresholdHC/LatentDisintegration/Disintegration.lean):
  split $G$ at $P=1/2$, push the upper part forward by `gapOf` to a measure
  $\nu_+\le\mu$, take $q=\min(1,d\nu_+/d\mu)$, and identify $G_{\mu,q}$ with $G$
  on bounded measurable tests; then pass from `gapOf` to the real magnitude law
  through a measurable embedding.
- [`Full.lean`](../../lean/ThresholdHC/LatentDisintegration/Full.lean): the four
  targets, with `LatentThreshold.threshold_mean` for the target.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_latent_disintegration.py --replay --jobs 2` | 7 exact statements (the 4 targets and 3 components) and 28 transitive axiom reports over the 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [latent-disintegration-audit.log](latent-disintegration-audit.log) |
| `python -m unittest discover -s tools -p 'test_latent_disintegration.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 20,246 constants (16,348 theorems) in 1,689 modules, same axioms. 155 exported instances; 6 registered orphans, unchanged. 3,752 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,690 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 5
entries to `tools/definition_lock.json`: the four statements and `gapOf`. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which judged
the proposed statements not faithful as written and replaced them: the
magnitude law is read on $\mathbb R$ so that no default value enters the
headline statements, the class statement drops a redundant probability
hypothesis, and the target statement covers every representing $q$. A third
agent wrote the proofs. Before the specification was pinned, a fourth agent
that had not written them:
- rebuilt the modules and printed the axioms of all public declarations;
- checked the statements against `eq:model`, `eq:target` and `eq:modulus-intro`;
- checked that $\mu=\delta_{1/4}$, $q=1/3$ gives $G(P>1/2)=1/3$, and that the point mass at $P=1/2$ lies in no class, so the equivalence is not trivial.

It found no defect in the Lean. Its two minor points concerned a source
citation in the specification's docstring, corrected before the pin, and the
location of the implementer's report. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
