# Formal scope

No new statistical theorem in this package is Lean formalized. The single-coin product theorem, its small-bias refinement, the raw-average consequence, population information direct sum, terminal testing consequence, radial construction, and pilot saddle theorem are paper proofs with separate agent review.

The fresh formal work here is verification and source preservation of concurrent Tier5 developments. Exact declaration/type mappings, assumptions,109 axiom reports, commands, timings, and the44-file closure are in audit/TIER5_COVERAGE.md and audit/tier5_replay.json. FINAL_PROOF_HASHES.json pins the separate paper sources; it is not a Lean certificate.

The nine checked declarations in namespace ThresholdHC.Tier5 are creation_law_total, creation_law_consistent, creation_finite_kl_bound, creation_stops, creation_kl_eq_iSup, creation_infinite_kl_bound, creation_observable_kl_bound, unbounded_creation_example and tier5_landmark. CurrentTier5Audit.lean elaborates each at its original locked exact type and prints the axioms of all109 roots. Only Classical.choice, Quot.sound and propext occurred. No sorry, admitted target, custom axiom or circular hypothesis was accepted by the unchanged validator.

Tier5 permits unboundedly many fresh labels across time and arbitrary revisits/interleaving. Its full-transcript conclusions assume RealizesCreationPrefixes and appropriate expected work; they do not supply universal construction of every hidden iid reservoir. Its sign priors1/2±eta with eta<=1/8 are balanced, not the global rare-event class. Its explicit nonvacuity example is specific. A successful rebuild therefore does not prove Psi minimax, rare-law existence, the radial estimator, or the single-coin entropy/product reduction.

The finite arithmetic checks use exact Python integers/Fractions but have no Lean correspondence. They certify the calculations actually enumerated, not the implementation's entire semantics or unrestricted infinite-horizon risk. The original v4/formal mapping is inherited from the earlier checkpoint, not silently extended here.
