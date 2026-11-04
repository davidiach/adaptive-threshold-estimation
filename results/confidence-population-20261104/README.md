# Confidence transfer for a single type of hidden coin

Under the common local Hellinger bound $h(P,Q)\le\kappa E_0 T$, the two
quarter-smoothed priors give a population KL bound of $(16/3)\kappa$ times
actual reference work. The [observable-prefix proof](../../lean/ThresholdHC/ConfidenceTransfer/Observable.lean)
covers arbitrary private seed spaces, natural-number coin labels, revisits
and interleaving. For a fixed finite tree the identity decomposes KL by
switching one slot at a time. Smoothing the prior preserves the rarity
restriction and halves the mean separation.

The [stopping argument](../../lean/ThresholdHC/ConfidenceTransfer/Terminal.lean)
recovers the full observable stopped seed and tape from their prefixes.
Expected work must be finite under each smoothed endpoint. The upper bound
charges only the reference endpoint. A uniform expected budget supplies both
conditions.

Given the note’s quantitative common-pair premise for all capped randomized
local policies, the [minimax theorem](../../lean/ThresholdHC/ConfidenceTransfer/CommonPairRate.lean)
gives the coefficient $1/128$ in front of $\min(b,\sqrt{J\log(1/\delta)/B})$.
It covers every observable estimator and its uniform error guarantee on the
globally rare class. The hypothesis requires one pair before the policy is
chosen. A derivation of that exact common-pair premise from a supplied
variance–work obstruction is a separate obligation. The adaptive multi-type
extension, additive localization and hard-budget median are outside this audit.

The integer label of each [compiler log](status.json) matches a recorded step.
The build used the pinned Mathlib inputs, reused 311 project artifacts checked
against the earlier records, and rebuilt 12 project modules, including five
older confidence dependencies. The [audit input](ExactAudit.lean) contains six
exact type checks and the [kernel output](13.log) covers 21 transitive axiom
reports. All reports use only propext, Classical.choice and Quot.sound.

Run `python tools/verify_confidence_population.py` from the repository root.
