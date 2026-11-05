# Finite-cell observed-state lower bound

The [full theorem](../../lean/ThresholdHC/ObservedState/Finite.lean)
constructs a finite measurable partition of the uniform state space and
proves the exact confidence lower bound for arbitrary selected-state
algorithms. The proof checkpoint is
[7351171](https://github.com/davidiach/adaptive-threshold-estimation/commit/73511713e46e71ac977e191bb128cdd8e951ff64).
Source and compiled-object identities are in [status.json](status.json).

## Audit scope

- Twenty-two independent exact-type checks and 58 transitive axiom reports passed.
- All 16 new modules compiled natively with the pinned Lean toolchain and empty compiler logs.
- The dependency closure contains 176 project modules. Of 160 inherited objects, 145 match previously published hashes and 15 are identified for the first time in this record. Every inherited source matches the base checkpoint.
- The full theorem constructs the partition, magnitude envelope and target separation.
- The experiment permits arbitrary measurable point queries, revisits, interleaving, private randomness and unbounded stopping.
- The audit identifies the actual conditional mean, threshold target and expected number of physical observations.
- The lower coefficient is \(225/(128h^2)\) multiplying \(\operatorname{kl}(1-2\delta,2\delta)\).

The complete source and object hashes, exact compiler inputs, compiler
output and audit reports are retained here. The allowed axiom set is
`propext`, `Classical.choice`, and `Quot.sound`.

The construction uses the second-moment replication condition
\(M^{-1}\le\delta\Delta^2/16\). The paper's Hoeffding-based replication
count and continuous-magnitude extension retain their separate paper proofs.

The [proof guide](../../docs/OBSERVED_STATES.md) records the module map.
Run `python tools/verify_observed_states.py` for a fresh audit.
[Appendix X](../../paper/v6/appendix-finite-observed.tex) presents the argument.
The [published manuscript](../../paper/v6/builds/finite-observed-20261105.pdf)
has 150 pages. Its [build manifest](../../paper/v6/builds/finite-observed-20261105.json)
records byte-identical independent builds, source identities and visual checks.

CI on later publication commits is reported on
[PR #53](https://github.com/davidiach/adaptive-threshold-estimation/pull/53).
