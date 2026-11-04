# Quarter smoothing for arbitrary probability measures

Let A and C be the mixtures with respective weights (3/4, 1/4) and (1/4, 3/4)
of probability measures P and Q on a common measurable space. Both KL(A‖C)
and KL(C‖A) are bounded by 8/3 times one minus the Hellinger affinity of P
and Q. The original measures may be singular. This checks Lemma 1 of the
[confidence-transfer note](../../research/2026-10-30-confidence-transfer/NOTE.md).

The [statement](https://github.com/davidiach/adaptive-threshold-estimation/blob/491dfc246265199e5108868184ccd0c3d7a56010/lean/ThresholdHC/ConfidenceTransfer/Specification.lean)
uses the project's existing affinity relative to P + Q. The
[proof](https://github.com/davidiach/adaptive-threshold-estimation/blob/680a833415e8de803d2a98847292063f10448527/lean/ThresholdHC/ConfidenceTransfer/Quarter.lean)
bounds the KL density pointwise and integrates it over this dominating measure.

The [isolated audit](status.json) rebuilt all three project modules, including
the affinity definition, against the pinned Mathlib cache. The [kernel input](ExactAudit.lean)
checks the locked proposition and the expanded inequality. Its five
[axiom reports](04.log) contain only propext, Classical.choice and Quot.sound.
From the repository root run `python tools/verify_quarter_smoothing.py`.
