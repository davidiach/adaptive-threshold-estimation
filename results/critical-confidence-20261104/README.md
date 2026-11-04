# Critical-law confidence lower bound

For the fixed density $32d$ on $(0,1/4]$, write $L=1+\log(1/\rho)$.
For some universal $c>0$, the minimax confidence radius under a uniform
expected flip budget is at least
$$
 c\min\{\rho,\sqrt{\rho L(1+\log L)\log(1/\delta)/B}\}.
$$
The statement covers $0<\rho,\delta\le1/4$, every $B>0$ and all observable
adaptive estimators. The same bound applies to any smaller class of estimators
with a deterministic cap. The [proof](../../lean/ThresholdHC/ConfidenceTransfer/CriticalRate.lean)
constructs the common pair from the existing critical-law theorem and then
uses the [single-type transfer](../confidence-population-20261104/README.md).
The [change of parameter space](../../lean/ThresholdHC/ConfidenceTransfer/CriticalModel.lean)
preserves the Bernoulli parameter law, the complete capped word and expected null work.

The [native record](status.json) checks all 323 inherited project objects against
the preceding audit. The two new modules and the [exact statements](ExactAudit.lean)
compiled successfully. The [kernel output](03.log) contains 12 transitive axiom
reports using only propext, Classical.choice and Quot.sound.

Run `python tools/verify_critical_confidence.py` from the repository root.
The matching high-confidence upper bound uses the paper's capped-median construction.
