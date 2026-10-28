# Mathematical review guide

Date: 28 October 2026.

## What this bundle asks a reviewer to assess

The principal claim is a joint, universal-constant characterization of minimax RMS risk for every known magnitude law, every \(0<\rho\le1/4\), and every \(B>0\). The analytical split between entropy cost and truncated inverse-gap cost must be attainable using observed flips alone. The lower bound must cover arbitrary interleaving and stopping under a uniform expected-work budget.

The second claim is a robust stopping-program characterization with an exact four-prior dual, controlled comparison with adaptive minimax risk, and convergent finite certificates. Its numerical examples support the certificate implementation. They do not establish the general theorem.

Separate **model audits** of the scalar upper and lower dependency chains have been completed, together with a targeted primary-source novelty comparison. No substantive blocker was found in the chains examined. The consolidation now includes the specialized dependencies within its appendices. **External human mathematical refereeing remains outstanding.** The new arbitrary-law and dual/bracketing results are not claimed to be formally verified. Formal results in the author's earlier baseline have their own narrower scope.

## Contribution boundaries

| Part | Prior work or inherited input | Claim to examine here |
|---|---|---|
| Entropy–tail characterization | Baseline rare phase results and critical entropy correction | Joint selection formula for arbitrary known laws, including atoms and infinite full-law entropy |
| Weighted sign entropy | Chen–Li gap entropy; Chen–Li–Qiao Lemma 4.1 and Remark D.4 | Adaptation to the exact finite-gap hypotheses, followed by scale-sensitive saturation and packing |
| Robust four-prior dual | Lee–Valiant triangular walks and information/work optimization; convex estimation/testing duality | Exact identity for separate worst-case bias, moment, and work constraints; attainment and reference absorption |
| Adaptive transfer | Lee–Valiant decomposition and the baseline common-pair argument | Uniform midpoint work accounting and compatible additive localization for the full class |
| Convergent finite brackets | Lee–Valiant's reveal-at-cap strengthening | Monotone robust upper/lower programs, convergence, and an eventual sufficient cap criterion |
| Fixed-cap bias floor | Binomial moment matching and interpolation | Odd-moment target diameter for this known paired-support model; a secondary consequence |

The pinned baseline already attributes its finite-gap entropy mechanism to Chen–Li–Qiao and disclaims novelty for that mechanism. The related-work section preserves this history. The literature check did not locate the full arbitrary-law selection formula with the same model and quantifiers; it does not certify priority. The dated source index is [review/novelty_sources.json](review/novelty_sources.json).

## Efficient reading order

Start with the model and the theorem “An entropy–tail law for the full joint problem.” Then read the mixed upper construction in `sections/additive.tex` and the matching packing proof in `sections/matching_lower.tex`.

For their dependencies, consult `upper_foundations.tex`, `lower_foundations.tex`, and `transfer_foundations.tex` within `sections/`. The first supplies actual observable procedures; the second supplies one-unit null-work obstructions; the third obtains common hard pairs and transfers them to population algorithms. These appendices make earlier unpublished notes unnecessary for checking the chain.

Read `dual_transfer.tex`, `genie_brackets.tex`, and `flow_foundations.tex` for the stopping-program claims. `identifiability.tex` gives the fixed-cap corollary. `checks/README.md` explains which numerical inequalities the stored rational certificates establish.

## Four pointed review questions

### 1. Does the upper construction preserve the hidden-unit experiment?

Check that every likelihood ratio is evaluated on an actual observed prefix, with a null mixture using the full known law. The analytical decomposition \(\mu=\sigma+\tau+\zeta\) must not become an observable component label. The global bound \(\int q\,d\mu\le\rho\) must never be replaced by a pointwise assumption \(q(d)\le\rho\).

In the race, odd/even streams must share the original latent unit. Adjacent-level corrections must use unused observations from that same unit; different replications use fresh units. Confirm error control even when the reference bank does not terminate outside its selected submeasure, the singular endpoint \(d=1/2\), and compound-Poisson variance based on raw second moments. The intensity may be below one, as required for every \(B>0\).

### 2. Is the hard pair genuinely common to all local policies, and is work charged under the correct law?

Inspect the quantifier order in the bias-indexed transfer: one pair must work for every capped randomized local policy. The finite-mixture argument, weak-star compactness, noisy finite partitions, and subsequent limit must justify arbitrary auxiliary seeds.

Then inspect the midpoint product decomposition for interleaved observations. The uniform budget is needed at the midpoint; a bound only at the endpoints would not suffice. Null-to-midpoint domination must have the correct direction, and summing local work must charge each purchased observation once. For localization, the simulated component is retained on revisits. Finally, finite expected endpoint work must justify passing from fixed global caps to terminal decisions without assuming termination under the fair coin.

### 3. Does the lower packing retain both rarity constraints and actual mass saturation?

Check that finite selection minimizes the uncapped inner objective. Distinguish exact inverse-square integral entropy from canonical endpoint entropy; their comparison changes the functional, not the observation channel.

For a component of mass \(\tau_i\), conditional entropy and minimum band mass are \(G_i/\tau_i\) and \(w_{*,i}/\tau_i\). The lower product therefore contains \(\min\{\theta_iG_i,\tau_i w_{*,i}/a_i^2\}\). Verify both \(\theta_i\le w_{*,i}/4\le\tau_i/4\) and \(\sum_i\theta_i\le\rho\). The scale factor in the saturation branch comes from the information gate; all rejected restart work is charged, and its output scaling cannot use the unknown conditional activation probability. For infinite laws, confirm that finite-prefix approximation uses vanishing omitted probability mass and needs neither finite full entropy nor a positive limiting minimum band mass.

### 4. Do the exact dual and genie limits justify the unrestricted risk bracket?

Check strict relative feasibility, attainment, and the closed-perspective conventions at impossible states in the robust flow program. The variance-reference and work-reference priors have separate roles; any replacement by endpoint mixtures requires the stated quantitative argument.

For the genie, latent revelation is a stronger lower-bound experiment, not an implementable upper estimator. Inspect the compactness/semicontinuity argument establishing \(G_N\uparrow P_\infty\) and \(P_N\downarrow P_\infty\). A fixed-cap ordinary dual alone is not a lower certificate for the unrestricted problem. The verified bounds must have the orientation \(L_N\le G_N\le P_\infty\le P_N\le U_N\); the additional adaptive comparison yields \(L_N/8\le R\le U_N\). The exact check \(U_N^2\le4L_N^2\) then supports the stated factor-16 bracket. No uniform cap-convergence rate or sharp scalar comparison constant is claimed.

## Scope of a useful external report

A useful report would identify any failed quantifier, uncharged observation, inadmissible prior, or unjustified limiting passage in these four transitions, and distinguish a proof gap from an exposition issue. It should also assess whether a more general published experiment-design result subsumes the robust dual, beyond the primary antecedents already documented. The source bundle is ready for that review; no external review is represented as having occurred.


## Referee revision checklist (29 October 2026)

The principal conclusions retain their original scope. Check the finite-C_v
qualification and explicit failure example in the monotone genie theorem,
and keep epsilon fixed before taking the cap limit in the optimized theorem.
Also inspect the revised 214 sign-entropy arithmetic, ordinary mass bound rho,
factor-two dyadic selection, explicit Psi optimizer, and the new worked examples.
Use theorem labels rather than historical theorem numbers, which may shift
after the inserted propositions and remarks. Current verification results are
in `VERIFICATION.json`; the prior build record is retained only as provenance.
