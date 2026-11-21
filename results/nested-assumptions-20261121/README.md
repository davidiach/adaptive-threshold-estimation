# The nested-simulation class and the Giles–Haji-Ali assumptions: library audit

The last sentence of Corollary `cor:nested` of the v6 paper
([`paper/v6/core.tex`](../../paper/v6/core.tex), *Critical nested-simulation
obstruction*) says that every measurable conditional model with
$U\sim\mathrm{Unif}[0,1]$, $X\in\{-1,1\}$ and
$D(U)=|E[X\mid U]|/2\sim\mathrm{Unif}(0,1/4]$, and no cross-state
regularity, satisfies Assumptions 2.1 and 2.4 of Giles and Haji-Ali
([arXiv:1802.05016v2](https://arxiv.org/abs/1802.05016)) with uniform
constants. The checked continuous-state lower bounds proved the density and
moment bounds for the hard designs only. Lean now checks the class-wide
statement, in
[`lean/ThresholdHC/NestedAssumptions`](../../lean/ThresholdHC/NestedAssumptions/Full.lean).
The `ContinuousObserved` group and the paper are unchanged. The audit runs
below were made at commit
[`ae16cd0`](https://github.com/davidiach/adaptive-threshold-estimation/commit/ae16cd0).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/NestedAssumptions/Specification.lean)
represents conditional laws by a state-indexed kernel $K:\Omega\to$ laws on
$\mathbb R$ and defines:

- `GHABoundedDensity P K ρ₀ δ₀`: the normalized absolute conditional mean
  $|E[X\mid Y]|/\sigma(Y)$ is measurable and has a density at most $\rho_0$
  on $[0,\delta_0]$ (Assumption 2.1);
- `GHAStandardizedMoment P K q C`: at order $q>2$ the conditional standardized
  $q$th central absolute moment is at most $C$, almost everywhere, with
  $\sigma>0$ and integrability required (Assumption 2.4);
- `NestedModel p`: a measurable $p$ with $P(X=1\mid U=u)=p(u)$, $U$ uniform on
  $[0,1]$, and $D(U)$ uniform on $(0,1/4]$.

| Target | Statement |
|---|---|
| `nested_assumptions` | Every model of the class satisfies Assumption 2.1 with $\rho_0=2$ at every $\delta_0>0$ and Assumption 2.4 at every $q>2$ with $C=3^{q/2}$. |
| `uniform_constants` | There are $\rho_0,\delta_0,q,C$, chosen before the model, that work for every model of the class. |
| `hard_design_nested` | Every sign-cell design of the checked lower bounds `uniform_confidence_lower` and `uniform_rms_lower`, with every sign array, is a model of the class. |
| `hard_design_law` | The class kernel of such a design is the per-query observation law that the lower bounds use, by definition. |
| `nested_model_nonempty` | The class is inhabited. |

The guards in the two predicates rule out values that Lean assigns by
convention: an undefined integral is $0$, $x/0=0$, and the image of a
non-measurable map is a Dirac measure. The constants are stronger than the
corollary needs.

## How the proofs go

[`Binary.lean`](../../lean/ThresholdHC/NestedAssumptions/Binary.lean)
computes the conditional mean $2p-1$, variance $1-(2p-1)^2$ and
$D=|p-1/2|$ of the binary law and bounds the standardized moment by
$3^{q/2}$ when $D\le1/4$.
[`Model.lean`](../../lean/ThresholdHC/NestedAssumptions/Model.lean) writes the
normalized mean as the checked change of variables
$Z(D)=2D/\sqrt{1-4D^2}$ applied to $D(U)$, so its law has the checked density
$2/(1+z^2)^{3/2}\le2$.
[`HardDesign.lean`](../../lean/ThresholdHC/NestedAssumptions/HardDesign.lean)
reuses the exact uniform gap law of `ContinuousObserved` for the hard
designs, and [`Full.lean`](../../lean/ThresholdHC/NestedAssumptions/Full.lean)
assembles the targets.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_nested_assumptions.py --replay --jobs 3` | 8 exact statements (the 5 targets and 3 components) and 36 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [nested-assumptions-audit.log](nested-assumptions-audit.log) |
| `python -m unittest discover -s tools -p 'test_nested_assumptions.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,192 constants (14,639 theorems) in 1,553 modules, same axioms. 151 exported instances, one of them the group's named, global, Prop-valued probability instance of the binary law; 6 registered orphans, unchanged. 3,412 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,554 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 12
entries to `tools/definition_lock.json`: the conditional mean, standard
deviation and normalized mean, the two assumption predicates, the binary law,
the class and the five statements. No existing entry changed. The run
recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The two predicates transcribe the three
in-repository paraphrases of Assumptions 2.1 and 2.4
([source audit](../../inputs/next-phase/baseline/Adaptive_Threshold_v4/review/SOURCE_AUDIT.md),
[literature audit](../../research/2026-10-27-minimax-audit/LITERATURE_AUDIT.md),
[Route A sources](../../research/2026-10-27-route-a/sources.md)), which agree with
each other; they have not been compared with the verbatim text of the paper.
If Assumption 2.1 bounds the density of the signed ratio
$E[X\mid Y]/\sigma(Y)$, the definition would change; the absolute-ratio
density with a global bound implies the signed and distribution-function
readings with the same constant. Assumption 2.4 is stated almost
everywhere; a pointwise reading would fail for class members modified on a
null set. The rate asymptotic of the corollary is the checked
`uniform_confidence_lower`, `uniform_rms_lower` and upper transfer, and is not
restated.

## Review

The item was planned by one agent, criticized by a second, which added the
nonemptiness and law-identification targets and fixed the density step, and
written by a third. Before the specification was pinned, a fourth agent that
had not written the proofs rebuilt the modules, printed the axioms, ran the
audit's scans and probed non-vacuity: the constant model $p=1/2$ is not in
the class, the degenerate kernel at $0$ fails both predicates, and the
binary model with $p=3/4$ fails the density predicate, so conventional
values make the predicates fail rather than hold vacuously. It found one
minor point: the specification placed the appendix calculation after the
wrong proof. It was reworded before this audit. These were reviews by AI
agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
