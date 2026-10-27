# Claim dependency graph

```mermaid
graph TD
  Model[Hidden iid reservoir, global rarity, charged flips] --> Err[Finite asymmetric tests: supermartingale crossing and bounded-observation concentration]
  Err --> Rearr[Global-rarity upper-tail rearrangement]
  Rearr --> Critical[Critical quadratic envelope: EY2 at most 165rho/56; work at most 1350 a^-2 L H]
  Critical --> Budget[Independent Poisson replication and optional clipping]
  Budget --> Confidence[Median confidence amplification]
  Err --> Arbitrary[Finite arbitrary-law upper bracket]
  Channel[Bounded observations and log concavity] --> Err
  LV[Lee-Valiant v3 Cor19: audited external theorem] --> Hybrid[Bounded-ratio finite-prefix decomposition]
  Model --> Hybrid
  Hybrid --> Lower[Inherited Psi statistical lower: paper only]
  Optimizer[Locked Tier3 optimizer: Lean] --> Psi[Exact Psi value]
  Lower --> Gap[Critical residual factor sqrt H; arbitrary-law upper unresolved]
  Psi --> Gap
  Critical --> Gap
  Finite[Finite-prefix information bound] --> Bridge[Terminal testing with separately established stopping]
  Walk[Exact random-walk counterexample: paper] --> NoTransfer[One-law work cannot transfer termination]
  Bridge --> Lower
  GHA[GHA v2 assumptions and observed-state oracle] --> Class[Fixed union of finite cell models with uniform constants]
  Class --> Nested[Inherited squared-log lower scope]
  Regression[Observed shared-parameter example] --> Boundary[Cross-state structure can remove logarithm]
```

New paper roots: critical, arbitrary bracket, bounded-channel extension, stopping counterexample/testing bridge, qualified known-gap adaptation. No new complete Lean statistical root is claimed. Exact arithmetic diagnostics are leaves checking finite instances, not proof dependencies for universal statements.

Formal dependency closures and standard axiom checks are in `formal/`; the old locks were checked, not regenerated. The paper-extension specification has a separate lock. Empirical results depend on the preregistered source hash, independent final seed families, original-real oracle check, and cost/calibration contract. Historical baseline replay and new held-out data are distinct nodes.
