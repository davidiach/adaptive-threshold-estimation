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

The full 713 extension has its own specification, first published in checkpoint
`8a435ec` before the final proof. Its SHA-256 remains
`a3fd9513084b2168cf86fe74962c14df956970c28ff270795591cf45037d9a86`.
The completion guard checks this hash, requires the proof to inhabit that exact
statement, builds all registered modules, and independently audits every public
proof root and the final theorem's transitive axioms. Source hashes are checked
before and after the audit. Three parallel agents developed supporting modules;
separate source reviews checked the model assumptions and final assembly.
The 12 original frozen files and all benchmark locks remain unchanged.
