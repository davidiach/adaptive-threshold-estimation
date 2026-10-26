# Response to the final Opus review

All substantive integration recommendations were adopted, subject to the scope distinctions below.

| Review item | Consolidated treatment |
|---|---|
| Promote unknown-margin adaptation | Theorem 1 and Section 5 now state and prove the common budget-only algorithm. |
| Credit Haldane | Added the 1945 Biometrika citation; the exact inverse-moment identity is reproved and not claimed as new. |
| Use the symmetric-KL converse | Section 6 uses both transcript KL directions plus 8H² ≤ KL(P,Q)+KL(Q,P), under H²=1−affinity. |
| Add the reverse-direction argument | The posterior lemma explicitly applies the Taylor upper bound with the endpoint arguments interchanged. |
| Remove superseded full-range information bound | The retained bound is 32d²η²/(1−4η²)², not the older chi-square constant. |
| Drop the finite-prefix proof | It is omitted entirely, avoiding its extra regularity and Hellinger-notation issues. |
| Retain the local smoothness cutoff | The smooth-density proof uses a0=1/4 independently of the global a=1/2. |
| Integrate the continuous nested embedding | Early Corollary 4 and Section 9.1 verify both GHA assumptions with constants independent of the accuracy scale. |
| Preserve realistic positioning | No landmark claim, no “first” claim, no rare-event theorem, no assertion that specialist review is complete. |

## Wording qualifications

The nested-simulation conclusion is stated as a **worst-case sample-oracle lower bound on a hard subclass satisfying the cited assumptions**. This is stronger and more precise than a rate analogy, but it is not an assertion that every structured conditional model or every information oracle has that lower complexity.

The coefficient 1/16 is the best possible coefficient in a lower inequality valid for every magnitude law. Fixed-gap laws attain it. The manuscript does not claim that the exact optimal product equals Iμ²/16 for every nondegenerate law.

Distribution-blind adaptation applies to the budget-indexed risk rule. It does not identify an observable confidence radius or determine a budget for an arbitrary requested error without extra distributional information.

The new draft integrates reviewed components and includes additional local and computational checks. It has not received an independent specialist review as a consolidated document.
