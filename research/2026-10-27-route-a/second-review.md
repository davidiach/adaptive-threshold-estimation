# Second analytic review of the power-margin construction

Date: 2026-10-27. Reviewer: the formal-foundations agent, acting here as a second analytic reviewer. I did not author `construction.tex` or its mathematical specification. I did author the separate Uniform713 moment bridge, which is not used in this new upper proof. This is a separate agent pass, not external specialist review; model diversity is not guaranteed.

Reviewed manuscript snapshot: SHA256 `f53c55f8ae8d3996682bb8460ebea9b68fef9e372fed0187a44b71a0e0c1fd8c`. The product-space realization paragraph is included in this snapshot. Any subsequently reviewed amendments are recorded below.

**Finding:** no blocking defect found in the stated upper theorem for the margin class with fixed exponent α>2. The constants and uniform expected-work claim survived this pass. This is paper-proof review, not Lean verification of the new theorem. The imported fixed-gap lower theorem is the primary-source reviewer's responsibility; I reviewed the simulation reduction but do not independently certify that source's full theorem/proof.

## What I checked

1. **Observation access and finite implementation.** The algorithm uses only known a,ρ, an independent random seed, and observed head counts. For k≥n≥1, n2^(-k)≤1/2, so neither likelihood process can reach a threshold: its value is below 2 while even the smaller threshold is at least 4. Checking k<n is therefore exactly equivalent to the infinite-dictionary definition. The newly added countable product of independent D,U,V variables realizes arbitrary measurable μ,q. Its latent uniforms and gaps remain outside the policy inputs.

2. **False classifications.** A wrong-sign likelihood factor has conditional expectation 1−4rd≤1. Bounded-horizon stopping of this nonnegative supermartingale gives the crossing bound without unjustified unbounded optional stopping. Summing weights π_k=2^(-k-1) gives conditional errors ε for positives and ρε for negatives, including D=1/2. The negative-priority tie convention preserves both bounds.

3. **Stopping-time integrability.** With x=min(d,a) and k=ceil(log₂(a/x)), r is between x/4 and x/2. The stated elementary logarithm bounds give mean correct-sign log increment at least (2/3)x². Upward overshoot is below 1. The stopped-sum identity is used only at σ∧N; its event {σ≥i} is determined before increment i. The pathwise upper bound A+1 then controls E(σ∧N), and monotone convergence proves finite Eσ before an unbounded stopping identity is needed. This validates the 3/2 factor and c₀=1+2log2.

4. **The global rarity constraint.** The critical step is the layer-cake bound

   E[qx⁻²] ≤ a⁻²ρ + ∫_(a⁻²)^∞ min(ρ,(a²u)^(-α/2)) du = A₀a⁻²ρ^(1−2/α).

   This uses q≤1 and E q≤ρ separately; it never substitutes q≤ρ or E(qx⁻²)≤ρE(x⁻²). Its exact-power extremizer places positives on the smallest gaps, the most hostile location for work. The other two integrals give A₀=α/(α−2) and A₁=α/(α−2)². Atoms at or above a are covered by x=min(D,a). All integrations are nonnegative until their finiteness is established.

5. **Removal of the log-rarity cost.** The factor log(1/ρ) is paid only when S=1. Its global contribution is bounded by A₀a⁻²ρ^β log(1/ρ), β=1−2/α>0. The elementary supremum sup_(t≥0) t exp(−βt)=1/(eβ) is valid uniformly for all supplied ρ≤1/4. This is exactly the step that fails at α=2; the theorem does not conceal that dependence.

6. **Same-tape correction.** Both thresholds multiply by 16 between levels, so the first crossing time is pathwise nondecreasing. Monitoring both needed classifiers on one tape costs T_J, not T_J+T_(J−1), and the earlier decision can be stored. No independence between levels is assumed. Their disagreements imply an error relative to the same latent sign.

7. **Exact constants and unbiasedness.** The zero-level contribution is at most 17ρ/8. The remaining second-moment series is at most (17ρ/4)∑_(j≥1)8^(−j)=17ρ/28. Their sum is exactly 153ρ/56. The geometric level has E(J+1)=2, making its averaged log(1/ε_J) equal to 8log2. Adding c₀ gives precisely 1+10log2 in w_α. Nonnegative summation establishes the second moment first; absolute summability then justifies the signed telescope and its limit θ.

8. **Budget and saturation.** For λ=Ba²/w_α, an independent Poisson number of fresh-coin copies has expected total work ≤B and estimator variance E(Y²)/λ. The latter is the second moment, not Var(Y), as required for a compound-Poisson sum. These identities remain correct for λ<1. Clipping to [0,ρ] reduces squared error for every allowed θ. Selecting the constant ρ/2 whenever its guaranteed bound is smaller yields the stated minimum, without assuming a positive integer batch count or silently exceeding B.

9. **Parameter independence.** The single-coin estimator depends on a,ρ, not μ,q or α. Calibration uses α,a,ρ,B. The proof is therefore uniform over the stated margin class. Changing ρ changes the estimator; its behavior at θ=0 does not contradict the existing impossibility for an estimator independent of ρ. No claim is made for all arbitrary laws or constants uniform as α decreases to 2.

10. **Lower-bound reduction and Ψ comparison.** Restricting q to a constant makes D independent of the sign. A fixed-gap-a coin can then simulate a variable-gap coin by retaining a private independent D and degrading each flip using fresh independent randomness. Conditional flips remain iid with the correct parameter; revisiting, interleaving, expected work, and stopping are preserved. This reduction is valid. The lower theorem it invokes still requires the separate source audit. The constant-allocation lower bound for Ψ and the Cauchy–Schwarz upper bound have the stated direction; the comparison constants can depend on α through √A₀.

## Edge cases and requested amendments

- D=1/2 is harmless because every reference r_k≤1/4, so the classifier never takes the logarithm of zero. Each positive d has finite conditional expected stopping; integrability near zero follows from the margin assumption, not a global minimum gap.
- The Poisson variable is finite almost surely and each evaluated classifier stops almost surely. A finite random collection of them therefore stops almost surely, with the separately proved mean-work bound.
- The statement of genuinely unbounded work at a=D=1/2,S=1 is correct: all negative likelihoods decrease, while L⁺_(k,n)≤(3/2)^n and every positive threshold is at least 2/(ρε_j). Thus for every fixed n, sufficiently large j forces T_j>n; that level has positive selection probability. Within the rarity class one may take q≡ρ at the endpoint, which gives this event positive population probability. I suggested adding this explicit inequality to the manuscript.
- I reported one purely typographical extra comma before `du` in the layer-cake formula; it was corrected in the reviewed snapshot above. This did not change the proof.

No counterexample emerged from these checks. The main limitations remain explicit: α=2 and arbitrary laws are unresolved, the new theorem is not Lean-checked, and worldwide novelty requires more than the present literature and agent reviews.

## Reviewed amendments

The subsequent mathematical snapshot SHA256 `026df37c392326b5dc293d47f403bf8d5027e92a53c00085d93d6b480f55d991` adds a localized fixed-gap RMS lower lemma and replaces the unbounded-work example by the directly admissible q=0, μ=δ_(1/2) case. I reviewed both changes. The latter uses the smaller threshold 2/ε_j and is correct. Conditional on the precisely stated external KL input, the lower lemma's remaining steps check: u=bρ and v=γ min(ρ,√ρ/(a√B)) enforce the parameter class and all smallness conditions by universal choices of b,γ; for large a, revealing each fresh sign gives the stated Bernoulli KL upper bound; finite-prefix passage controls unbounded stopping; and KL≤1/8 gives TV≤1/4. The test-from-estimator argument actually gives R≥√(3/32)v, so the claimed R≥v/4 is conservative. I specifically asked the primary-source reviewer to check the imported KL orientation and original-prior work expectation. This analytic pass does not replace that check.

**Final source reviewed:** SHA256 `fc198251e6b3df21c1203b26e5b0591136742417ff7d8c1534070cee54deb62e`. I checked the amendments: the lower simulation now correctly conditions iid flips on both the sign and the privately sampled D (conditioning on sign alone would be false after mixing D); first-observation numbering is justified by deferred independent latent draws and a revisit dictionary; source credit, review status, and diagnostic limitations are explicit. The source-review agent separately confirmed the original-prior expected-work bound and KL orientation in Corollary 19/Lemma 18. No blocking finding remains in this analytic review of the final source. The upper proof is self-contained at paper level; the matching lower proof retains its stated imported-theorem dependency.

**Final presentation revision accepted:** SHA256 `f05b297a9885a9cd24c203256ce11b0da29eb7f98433f0561f448652d1dbb4fc`, independently recomputed after reading the changed displays and attribution paragraphs. The initial constants and margin inequalities are unchanged mathematically, with their layout split across lines. The manuscript now explicitly credits Vihola Theorem 3 for single-term randomization and Example 8 for Poisson replication, while retaining its direct calculations. These edits introduce no new mathematical claim into this review; source-location verification belongs to the source audit. The analytic acceptance above applies to this final hash.

**Compiled-source correction accepted:** current SHA256 `ff70296efd76f7b1fd0ac50d12eff1a22361b5bb566dc97c82836833640b3d00`. I read the corrected work-bound display and independently verified by a byte replacement and SHA256 comparison that its only change from the previous reviewed source is escaping the closing TeX brace in `A_0\{c_0+\log(1/\varepsilon)\}`. The replacement reconstructs the previous `f05b297...` hash exactly. This is a delimiter correction with no mathematical change. Analytic acceptance applies to this current source hash.
