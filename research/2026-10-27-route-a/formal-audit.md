# Formal foundations audit and separate-moment bridge

Date: 2026-10-27. This is a supporting foundation, **not a new minimax theorem or an improvement of 713**. The proof agent and adversarial reviewer are distinct agents; model diversity is not guaranteed and neither is external specialist review.

## Actual baseline

The inspected checkout is `threshold-hillclimb`, whose origin is now `https://github.com/davidiach/adaptive-threshold-estimation.git`. Its initial inspected HEAD was `06af2df`; concurrently produced documentation commits `33eeeff` and `12e73e5` appeared during this session. This agent did not create those commits or alter the prior documentation edits. New formal work is additive and its exact source hashes are recorded in `lean/ThresholdHC/ResearchRouteA/status.json`.

| Claim | Exact formal scope and evidence inspected | Remaining limitation |
|---|---|---|
| Full 713 estimator | `Uniform713.full_bound_713 : FullBound713Statement`; arbitrary conditional observation kernel, bounded independent observations, latent magnitude/sign law, integrable inverse gap. Recorded audit: 130 roots, exit 0. Specification hash `a3fd9513084b2168cf86fe74962c14df956970c28ff270795591cf45037d9a86`. | Exports a per-law product; its internal separate moment bounds were not separately exported. Does not prove realization/admissibility in a general fresh-coin policy model. |
| Tier 3 optimizer | `Tier3.arbitrary_law_optimizer : ArbitraryLawOptimizerStatement`; measurable allocations with an integral mass constraint, arbitrary probability law, no inverse-moment assumption. `OptimizerModel.lean` hash `36c085b6409b1355247d5127ab4ee9fdb94e621c1aac8379fb1f119d607cae49`. | A variational identity, not an estimator, oracle reduction, or statistical upper bound. |
| Tier 3 stopping | Policies have type `Seed → List Bool → Option (Fin m)`, and the process realizes their specified finite-prefix laws. Recorded Tier 3 audit: 11/11 targets, 152 roots, exit 0, no pending targets. | Fixed finite coin family. The example permits genuinely unbounded finite-mean stopping, but this does not remove the fixed-family restriction. |
| Tier 4 full transcript KL | `Tier4.infinite_kl_bound : InfiniteKLBoundStatement`, and KL finiteness/data processing. Recorded audit: 6/6 targets, 65 roots, exit 0, no pending targets. `Tier4/Model.lean` hash `2271691c5af1c4936accbb9a5c62b6ea5cbc3e6bdd718b0b44a958cd7a057214`. | Already completed at the current starting point. Still `Fin m` coins with deterministic gaps and sign priors `1/2 ± η`; not the rare-prior KL lemma or iid arbitrary-law creation model. |
| Paper minimax and unbiased converse | The exact algorithm-level statements remain paper proofs with the review limits described in `docs/RESULTS.md`. | Neither their combination nor the Tier 4 landmark formalizes the complete paper. |

Read-only comparison of recorded source, definition, and lock hashes against the current files found no mismatch: 23 Tier 3 entries, 19 Tier 4 entries, and 21 Uniform713 entries. This is an integrity comparison, not an independent kernel replay of those complete historical targets. The parent session runs the appropriate baseline regressions in a disposable copy preserving current bytes. Historical CI does not validate this new work.

## New exact statement

`ThresholdHC.ResearchRouteA.separate_moment_bounds` inhabits `SeparateMomentBoundsStatement`. Under **exactly the existing** `Uniform713.ObservationModel`, it concludes

\[
Y\in L^2,\qquad W\in L^1,\qquad
\mathbb E Y^2\le23 I,\qquad \mathbb E W\le31 I,
\quad I=\int D^{-1}\,d\nu.
\]

`ThresholdHC.ResearchRouteA.uniform_family_bounds` inhabits `UniformFamilyBoundsStatement`. Fix the conditional kernel, observation map, gap function, and sign function. For any nonempty family of latent probability laws `ν γ` satisfying that model and sharing the same inverse moment `I`, it proves that both real ranges of variance and expected work are bounded above, that both suprema are nonnegative, and that

\[
\sup_\gamma\operatorname{Var}_{\nu_\gamma}(Y)\le23I,
\qquad \sup_\gamma\mathbb E_{\nu_\gamma}W\le31I,
\qquad
\bigl(\sup_\gamma\operatorname{Var}_{\nu_\gamma}(Y)\bigr)
\bigl(\sup_\gamma\mathbb E_{\nu_\gamma}W\bigr)\le713I^2.
\]

This is a **conditional observation-kernel family theorem**. It does not claim that every fresh-coin experiment has already been realized by that family. In the intended fixed-μ application, the family index would range over admissible `q`, the marginal of `D` would remain μ, and hence the common inverse moment would be automatic once realization is supplied. No supremum/infimum interchange occurs. The final inequality is non-strict: strict pointwise inequalities do not justify a strict bound for a supremum.

The proof reuses `conditional_bounds`, `integrate_conditional_inverse_gap`, measurability lemmas, and the variance/second-moment comparison. It copies the short conditional assembly from the existing full-bound proof into an additive module, exporting the information already proved there. No locked file was edited.

## Specification review, lock, and vacuity audit

Specification: `lean/ThresholdHC/ResearchRouteA/SeparateBoundsSpec.lean`.

- Specification SHA256: `d114a2734cfd0164def475115d0ebb25d1ba49c7f87bb96fa45e441c3eb40dbe`.
- Immutable v1 lock: `lean/ThresholdHC/ResearchRouteA/SPEC_LOCK_v1.json`.
- Lock SHA256: `1b8115cf053e978f35d28854544b9ed01d871a5c7bc4eedf936c13ceebe9d4c9`.
- The lock covers the complete local specification import closure, toolchain, library manifest, lake configuration, new verifier, and exact-type audit. It was written after independent specification review and before the acceptance replay.
- The independent adversarial agent found no blocking specification defect. Its review limits and optional suggestion to repeat integrability in the standalone family conclusion are recorded in that agent's review. The family theorem is advertised together with the separate-moment theorem, which explicitly concludes integrability.
- `0<D≤1/2` almost surely and probability-measure assumptions exclude division-by-zero and empty-measure escapes. Inverse integrability is a model assumption; upper-estimator integrability is a conclusion. No conversion of an infinite expectation to a real occurs.
- The real suprema have an explicitly nonempty index and proved bounded ranges. Both factors are proved nonnegative before multiplication.
- The actual definitions `uniformEstimator` and `uniformWork` ignore the latent first coordinate and use the observed `X` sequence and random level. They have no family-index argument. This observation is weaker than a proved policy implementation in a fresh-coin model.
- `Sanity.lean` gives a model and the resulting separate bounds for every real `0<d≤1/2` and both signs. Its observations are deterministic bounded observations, including Bernoulli(0)/Bernoulli(1) at `d=1/2`. The interior examples are **not** a construction of general Bernoulli tapes. They show satisfiability arbitrarily near zero; they do not replace the missing general realization theorem.
- This bridge asserts no new unbounded-stopping construction. The existing random-level estimator remains the object of its theorem, and the separate Tier 3 geometric-seed example supplies the previously recorded unbounded-stopping sanity check in its own model.

## Exact replay

From the repository root, in PowerShell:

```powershell
$env:ELAN_HOME = Join-Path (Get-Location) '.runtime/elan'
$env:PATH = "$env:ELAN_HOME\bin;$env:PATH"
$env:PYTHONUTF8 = '1'
python lean/ThresholdHC/ResearchRouteA/verify.py
```

The new verifier runs

```text
lake build ThresholdHC.ResearchRouteA.Sanity
lake env lean ThresholdHC/ResearchRouteA/Audit.lean
```

Both returned exit 0. It checks exact theorem types, all five public proof roots, source stability, full specification closure coverage, forbidden-proof-escape syntax, and transitive axioms. Every audited root used only `propext`, `Classical.choice`, and `Quot.sound`. Root coverage is five of five, not zero. Status is **Lean-checked against a specified target**. Logs and source hashes live beside the new modules, not in the published baseline `results/` files. The initial bare Python invocation failed before Lean with Windows executable lookup error because the parent PATH did not expose `lake`; the documented environment initialization resolved it without changing the locked sources. Prototype build also returned exit 0 before the lock; it was not counted as locked acceptance.

No new CI run was requested, and no independent external-machine replay of this bridge is available. The new verifier is separate and has not been substituted for any old frozen verifier.

A later redundant diagnostic invocation of `lake env lean ThresholdHC/ResearchRouteA/Audit.lean` was intentionally interrupted with Ctrl-C at the parent agent's request while the final official verifier was active and other concurrent formal work was present. That invocation returned exit 1 after interruption, with no compiler diagnostics; it is recorded as **interrupted**, not as a failed mathematical proof or a successful replay. It did not write source files or verification records and does not replace the earlier successful five-root audit. The parent's final verification record determines the later replay status.

## Shortest remaining formal dependency graph for Route A

1. Realize arbitrary measurable μ and q by iid latent draws and Bernoulli tapes on one explicit observable-history policy model. The policy's seed must be independent; fresh creation, revisiting, and interleaving require no globally fixed coin count.
2. Prove a canonical numbering/relabeling reduction. At observation prefix n, at most n coins have been observed. Integrate the appropriate finite-family law over iid gaps without revealing them to the policy.
3. Supply the actual rare-prior, single-coin information inequality and its transcript extension. The existing symmetric `1/2±η` Tier 4 statement cannot simply be renamed into this result. The literature audit is essential here.
4. For a proposed upper algorithm, prove observable implementation and its budget/moment bounds, uniformly over the **integral** rarity class. The optimizer alone provides none of these.

The new separate-moment bridge addresses a specific advertised uniformity gap for the existing unbiased construction. It does not remove steps 1–4 or settle the main research question.
