# Semantic audit of the round-two proof

This is a self-audit, not an independent review. The full argument and the
unformalized dependency boundary are in NOTE.md.

## Invalid shortcuts excluded

1. **Hellinger is not KL.** The pair `(1-e,e,0)` versus `(1-e,0,e)` has
   Hellinger square `e` and infinite directed KL. Quarter smoothing is an
   actual change to the hard instance, with a paid factor two in target
   separation, rather than a relabeling of the divergence.

2. **The population law is not affine.** The proof uses affineness only for
   one genuine coin while all other tapes are held at a fixed reference.
   The two-coin counterexample in NOTE.md and the exact algebra audit reject
   whole-population affineness.

3. **One common pair is required.** The imported premise is `exists pair,
   for every local policy and cap`. A separate difficult pair for each
   policy cannot be plugged into the hybrid decomposition.

4. **Reference work is actually admissible.** The new reference prior is a
   fixed convex combination of the original half-prior pair. It remains
   globally rare and pointwise at most one half. Null domination is used
   locally, with the other tapes held at that reference, and local reference
   costs sum to genuine population work. No global `2^N` domination and no
   average of endpoint work is substituted.

5. **Interleaving does not imply stopped-word independence.** The exact
   likelihood product is a leaf-density factorization conditional on the
   common action rule and seed. It does not assert independence of the
   adaptively stopped local words. Finite audits include interleaving.

6. **Types must be chosen before observation.** Each genuine coin's type
   is fixed before its first requested flip and persists on revisits. The
   type may depend on earlier coins' observed histories. Conditioning on
   that prehistory, not unconditional independence of type and seed, is
   used in the proof and represented by the finite fixtures.

7. **Unbounded stopping uses the same pair.** The pair is fixed for the
   given budget and confidence level before caps tend to infinity. Overflow
   probabilities are at most `B/N` at both admissible smoothed endpoints.

8. **Annular saturation is not discarded.** The imported minimum-band-mass
   branch remains in every `J_i`. The deterministic packing proof is reused
   at `B/log(1/delta)`, not bypassed by an inverse-moment heuristic.

9. **MSE amplification alone gives no lower bound.** The confidence lower
   argument is the new smoothing/KL transfer applied to actual common-pair
   obstructions. It is not deduced from the scalar RMS minimax statement.

10. **A mean work budget is not a hard cap.** The driver requests flips
    only up to each block's cap. A constant-probability timeout is included
    in each block's bad event before median amplification. Cost and output
    need not be independent within a block.

11. **Independent blocks are an assumption of the statistical guarantee.**
    The driver provides separate namespaces and RNG streams, but cannot
    certify factories that deliberately share hidden state. It does not
    receive or verify a base estimator's MSE proof. Its output record does
    not purport to certify a general-law statistical confidence interval.

12. **Arithmetic does not weaken the physical cap.** Work counters and
    scheduling comparisons use integers/Fractions. Rational output values
    are not rounded to floats. Display conversions in the demonstration are
    explicitly marked. Infinite/NaN outputs cause an error.

## Remaining assurance boundary

The universal proof still depends on the imported common-pair theorem,
null-work obstructions, and general-law packing/upper proofs. They have not
been independently re-proved or Lean-checked in this round. Finite tests and
exact interval arithmetic do not establish those universal statements.

No simultaneous-in-budget confidence sequence, unknown-law adaptivity,
wall-clock cap, practical optimal general-law estimator, or hard-budget RMS
equivalence has been proved. No wider-literature priority claim is made.
