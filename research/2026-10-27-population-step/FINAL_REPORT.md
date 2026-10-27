# Verified obstruction and population follow-up

The single-coin obstruction is sound in its stated class. The unrestricted arbitrary-law rare-event minimax problem remains unresolved. This pass makes the separation sharper and proves that one proposed route to an extra-logarithm population lower bound is wrong.

## Inherited result, independently verified

Fix a=1/4 and the exact quadratic gap law mu(dd)=2d/a^2 dd on(0,a]. Let L=1+log(1/rho), H=1+log L. For observable single-coin procedures with uniform bias at most rho/64, separate suprema V=sup_q Var_q(Y) and W=sup_q E_qT satisfy

`inf V W asymp rho L H`.

The same is true for the raw-second-moment product. The lower proof handles unbounded stopping, arbitrary thinning before the first flip, signed outputs, every moment/work tradeoff, and global rarity. The existing unbiased construction supplies the upper order. This is PROVED-ON-PAPER with adversarial agent review, not Lean formalized. The finite-grid entropy mechanism overlaps Chen–Li–Qiao; priority of the derived theorem is unresolved. Constants are universal only with a fixed at1/4, and the lower proof's effective asymptotic cutoff is extremely small.

The small-bias theorem was already present in concurrent work. This pass supplies an independently refined proof and its exact consequence: any raw deterministic average of n iid copies, even with a B-dependent kernel, achieving RMS epsilon<=rho/64 and uniform expected work B must satisfy `B epsilon^2 >= c rho L H`. This does not cover clipped or nonlinear outputs, interacting coins, unequal kernels with cancelling biases, or data-dependent replication.

## What the population attack established

**PROVED-ON-PAPER: a transferable information criterion.** A uniform directional Fisher-information/work inequality for every capped one-coin policy extends to arbitrary finite-prefix population creation and interleaving. A reference-law simulation argument supplies the reduction without giving the actual estimator q or latent magnitudes. With uniform expected work and termination at both endpoints, finite-prefix bounds imply an explicit terminal total-variation and RMS testing bound. The needed premise is an information upper bound, not the previously proved variance/work lower bound. The reduction uses factorized independent finite-history likelihoods and extends to other channels under its explicit regularity and one-coin premises.

**DISPROVED by paper proof: the natural radial extra-log information bound.** Set w_b(d)=min(1,b^2/d^2), Ew_b=rho, and q_eta=(1+eta)w_b/2 for |eta|<=1/2. An observable walk stopped at -1 or ceil(8a/b) has directional information/work ratio at least `a^2 rho/(32L)` in the supremum over finite-cap policies. Consequently this envelope cannot be O(a^2 rho/(L H)) uniformly as rho tends to zero. This refutes that particular proposed population converse, not the full Psi conjecture or an extra-log converse using other nuisance directions.

**PROVED-ON-PAPER: a positive calibrated radial result.** On that specified known-profile submodel, calibrating the walk's upper-hit indicator gives variance<=5.5rho L and uniform expected work<29. Centered independent Poisson replication gives

`R_radial(B) <= min(rho/4, sqrt(160 rho L/B))`.

Exact calibration integrals are permitted deterministic computation in the theoretical model. The proof includes termination, all work, and an explicit perturbation bound for approximate calibration. No actual numerical calibration or practical benchmark was run for this estimator. The result shows that hidden magnitudes by themselves do not force H on this submodel. It is not an arbitrary-q upper bound or a priority claim; scalar-mixture prior work may overlap.

**PROVED-ON-PAPER: a restricted pilot strategy cannot help.** For fixed unbiased features Y and zero-mean scalar Z with parameter-independent positive variance, an independent pilot choosing only the correction coefficient cannot improve minimax raw production MSE over the best fixed coefficient. The proof establishes coercivity and a saddle point directly. An implementable three-flip, two-gap estimator provides a nonvacuous example and exact checks. Its variance at q=0 can be427/16 in an explicit case, so it is rejected as a practical rare-event improvement.

## Computation, formal coverage, and practical limits

An exact Fraction dynamic program solved16 locked synthetic finite-prior Bayes problems at horizons1 through8, with independent labeled-history agreement in10 cases through5. At horizon8, adaptive allocation improves squared Bayes error by1.5917% and5.0307% over the better of fresh-only and single-coin-only policies. Those are finite deterministic-cap results, not expected-budget minimax bounds or held-out practical wins. The prior and program were locked before execution. Complete exact fractions and observable policies are retained.

The new Tier5 replay passed9 exact targets and109 axiom reports, with the standard allowlist only. Its44 audited dependency files are preserved. It genuinely goes beyond a fixed finite coin collection, but assumes supplied realized prefix laws and balanced sign priors; it neither constructs every arbitrary-law rare reservoir nor proves the new statistical results. All34 validator regressions and50 original-input checks passed. Original locks and v4 remain unchanged. See ACCEPTANCE.json for the final scoped check, not a historical success JSON.

No new broad practical benchmark or confidence-coverage claim is made. The preceding checkpoint's negative benchmark verdict remains negative. No external specialist has reviewed this work; correspondence remains an unsent draft.

## Exact remaining question

For arbitrary measurable q under the global rarity constraint, either construct a budget-dependent nonlinear population estimator matching Psi with proved uniform bias/risk/work/termination, or establish a population lower bound that incorporates multiple nuisance directions. The radial direction and fixed-feature pilot strategy are now resolved in their stated scopes. Clipping, adaptive acquisition, nonlinear aggregation, unequal-kernel cancellation and adaptive production counts remain possible routes; their mere possibility is not an upper bound. Arbitrary laws, sharp confidence dependence, and unknown-law/rarity adaptation remain separate unresolved obligations.

Publication uses a separate branch based on a8a8dc4 because another task committed d75c775 in the shared checkout during the pass. The package contains reviewed snapshots, not a silent endorsement or replacement of that later theorem. Only this new directory is committed by this pass; no v4 files, old validators, locks or shared checkout state are changed.
