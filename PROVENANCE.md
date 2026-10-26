# Research inputs and verification policy

This repository starts from the user-supplied `threshold-hillclimb-kit.zip`
and `Adaptive_Threshold_Next_Phase_Research_Package`. The original research
package is preserved under `inputs/next-phase/`. Its own integrity manifests
and original v4 files are retained. No novelty claim is made.

The starter kit's `BRIEF.md` describes the research tracks. Results distinguish
Lean kernel-checked proofs, paper arguments, numerical evidence, and conjectures.
Numerical sampling cannot certify a universally quantified theorem.

Target statements, scorers, and grids must not be weakened to improve scores.
Any compile-only correction is recorded in `FREEZE_LOG.md`; the formal freeze
is created only after the Lean compile gate succeeds. Until then, no valid
Lean score is claimed.

Constants are selected using the development grid. Benchmark configurations
are selected using tuning replications. Held-out data are used for acceptance
and reporting, not to guide subsequent candidate selection.

The initial import precedes the Lean compile gate so that the source baseline
is recorded before environment setup and research changes. Subsequent commits
record verified checkpoints and clearly labeled unsuccessful experiments.
Local runtimes and downloaded dependencies are excluded from Git.
