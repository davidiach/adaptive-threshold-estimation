# Consolidation log: v3 plus reviewed addenda → v4

## Theorems and model
- Global nonzero magnitude domain enlarged to (0,1/2], including deterministic coins.
- Theorem 1 now includes a single distribution-blind algorithm for all magnitude laws, rather than only a known-law or known-envelope allocation.
- Exact two-success cost calibration and its proof are integrated into the main upper-bound argument. Haldane inverse-binomial sampling is credited.
- Theorem 2 now has sharp universal lower coefficient 1/16. Its elementary symmetric-KL proof replaces both the original averaging-to-testing converse and the later finite-prefix Fisher/Hellinger proof.
- The already-proved separate conditional constants 85 (second moment) and 149 (work) are used, giving product upper coefficient 12665. These are analytic bounds, not empirical replacements.
- The full-range predictive bound states and proves both KL directions; its sharp leading coefficient is 32, with the necessary denominator (1−4η²)² retained.
- RMS and confidence lower constants updated to 1/64 and 15/(256√2).
- The envelope algorithm no longer needs the envelope as input.
- Fixed-gap corollary and the balanced/rare-event distinction made explicit.
- Nonnegative-output impossibility includes the deterministic-endpoint exception.
- Smooth-density construction preserves a0 = 1/4 and support in [1/4,3/4], with norm classes M ≥ Ms. No analytic/Gevrey extrapolation.
- Continuous-magnitude observed-state construction is integrated next to the finite-cell construction. An early corollary states the critical nested-simulation consequence and distinguishes RMS from fixed-confidence formulations.

## Presentation and provenance
- Superseded addendum proofs and workflow appendices removed from the main manuscript.
- Related work expanded: uniform and sequential nested simulation, later adaptive MLMC, discontinuous-function survey, sequential change of measure, unbiased smooth outer functions, and inverse sampling.
- Explicit limitations retained: expected rather than capped work; unknown distributional risk bound rather than observable radius; balanced worst cases; no cross-state regularity; no practical speedup or priority certification.
- Full numerical rerun performed with both predictive directions, deterministic endpoints, expanded classifier grid, and actual result logs.
- Updated implementation includes budget and confidence-amplified entry points; independent production sampling is preserved.
