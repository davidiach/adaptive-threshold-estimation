# Adaptive estimation of rare threshold proportions

This is the standalone source bundle for the consolidated research paper. Its main result characterizes minimax root-mean-square risk for every known magnitude law through an optimized entropy–tail functional. It also gives an exact four-prior stopping dual and convergent finite upper/lower certificates.

## Build the paper

Run from this directory with a working LaTeX installation and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The main source is `main.tex`; the resulting paper is `main.pdf`.

All specialized lemmas needed for the stated results are proved within this paper and its appendices. These include the observable classifiers and Poisson allocation, weighted sign testing and the scale-sensitive annular obstruction, finite convex comparison and adaptive localization, and stopping-flow representation and realization. Earlier research notes provide provenance; readers do not need to retrieve or work backward through them to follow the proofs or run the certificate checks. Standard mathematical tools and published antecedents remain explicitly cited.

## Observation model

A fresh unit has hidden magnitude \(D\sim\mu\) and hidden sign \(S\mid D=d\sim\operatorname{Ber}(q(d))\). Conditional on that fixed unit, observations are iid Bernoulli with mean \(1/2+(2S-1)d\). The statistician knows \(\mu,\rho,B\) and estimates \(\theta(q)=\int q\,d\mu\), uniformly over \(0\le q\le1\) with \(\theta(q)\le\rho\).

Every purchased observation costs one, including the first observation on a unit. The budget is expected total work, bounded uniformly over the parameter class. The benchmark allows revisiting, interleaving, randomization, nonlinear outputs, and unbounded stopping. Neither the magnitude nor the sign is available to an observable estimator. Latent-state revelation appears only in a strengthened experiment used to prove lower certificates.

## Check the stored numerical certificates

The numerical files and exact verifiers are preserved in `checks/`. Verification uses only the Python standard library; the recorded environment used Python 3.12. From this directory:

```sh
cd checks
python3 self_check_certificates.py
```

The bundled verification record reports 33 lower certificates, 9 upper policies, 9 stopping decisions, two analytic perfect-label checks, and rejection of six deliberately corrupted certificates. The verifiers rebuild the relevant quantities with rational arithmetic. They check the stated finite examples and do not constitute formal verification of the general mathematical theorems.

See [checks/README.md](checks/README.md) for individual verification commands, the meaning of the ordinary and genie certificates, and optional numerical-search instructions. Reproducing a numerical search requires the packages in `checks/requirements.txt`; verifying the stored certificates does not.

## Files and review status

| Path | Contents |
|---|---|
| `main.tex` | Paper entry point and bibliography |
| `sections/` | Main arguments and complete specialized appendices |
| `checks/` | Preserved numerical searches, exact verifiers, certificates, and verification records |
| [REVIEW_GUIDE.md](REVIEW_GUIDE.md) | Contribution boundaries, reading order, and four focused mathematical review questions |
| [review/novelty_sources.json](review/novelty_sources.json) | Dated primary-source index with theorem locations and inspection scope |

Separate model audits of the scalar upper and lower dependency chains and a targeted primary-source novelty comparison have been completed. They found no substantive blocker in the chains examined. External human mathematical refereeing remains outstanding. This bundle makes no formal-verification claim for its new general results.

The attribution distinguishes the new arbitrary-law selection theorem and robust certificate framework from established gap-entropy, adaptive-mixture, convex-duality, and optimal-stopping methods. In particular, the author's pinned version-5 critical proof already credited Chen–Li–Qiao for the sign-entropy mechanism; this consolidation preserves that attribution.

The baseline repository is [davidiach/adaptive-threshold-estimation](https://github.com/davidiach/adaptive-threshold-estimation), pinned at commit `eabf274cb42d4bff4daab6b58568ad6169e7f0a7`. Earlier phase results and the critical-law correction are baseline contributions, not newly claimed discoveries in this consolidation.


## Referee-audit revision (29 October 2026)

This is the revised manuscript, not the unchanged 28 October source bundle.
See `REVISION_NOTES.txt` for the applied recommendations and optional improvements.
The pointwise genie theorem explicitly assumes finite latent divergence;
the optimized genie convergence theorem retains its original scope.
The current build record is `VERIFICATION.json`. The inherited record is
preserved as `review/original_VERIFICATION_20261028.json` and is historical.

Run the independent revision checks with `python checks/verify_revisions.py`.
The stored certificate checks are unchanged and remain available under `checks/`.

The revised PDF was also built with Tectonic 0.17.0:

```sh
tectonic --untrusted --keep-logs --keep-intermediates main.tex
```

`REVISION_DIFF.patch` records changes to the original TeX sources.
The exact new finite example is displayed in the paper itself; `checks/revision_checks.json` provides narrower certified enclosures.


## Editorial update v2

This copy applies only the two minor editorial corrections identified by the
revision audit. See `EDITORIAL_FIXES.patch` and `REVISION_NOTES.txt`. The prior
revision remains separately preserved. Current build and preservation checks
are recorded in `VERIFICATION.json`.
