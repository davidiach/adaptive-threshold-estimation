# Observable hard-budget RMS reduction and minimax bounds

The [advance statement](../../lean/ThresholdHC/HardBudget/Specification.lean)
fixes the seed law, label namespaces, last-success output, pathwise flip cap
and mean squared error. The [generic theorem](../../lean/ThresholdHC/HardBudget/Full.lean)
proves it with $32C^2f(B)^2$ at $B\ge4$. For smaller budgets the controller
uses zero flips and returns the midpoint. A stage that stops exactly on its
cap counts as a success. The checked controller spends its full reservations
and discards filler flips after early success. Its result on every tape table
equals the clipped output of the most recent completed stage. Independence
is required between stages, while a stage's runtime may depend on its output.

| Application | Checked hard-cap RMS conclusion |
|---|---|
| [Ordinary, distribution-blind](../../lean/ThresholdHC/HardBudget/Ordinary.lean) | For $B\ge1$, the lower and upper coefficients on $\omega_\mu(B^{-1/2})$ are $1/64$ and $3000$. One upper family works for all gap laws. |
| [Known general law](../../lean/ThresholdHC/HardBudget/Rare.lean) | For every $B>0$ and $0<\rho\le1/4$, the coefficients on $K_{\mu,\rho}(B)$ are $10^{-17}$ and $160000$. Approximation of the expected-budget infimum uses the strict allowance $28001K$. |
| [Critical quadratic law](../../lean/ThresholdHC/HardBudget/Critical.lean) | A universal positive lower coefficient and upper coefficient $570000$ multiply $\min(\rho,\sqrt{\rho L(1+\log L)/B})$ at every positive budget. [Transport of observable laws](../../lean/ThresholdHC/HardBudget/CriticalTransport.lean) preserves the original critical expected work and RMS risk. |

The [native record](status.json) identifies 581 project dependencies. The
19 modules added for the reduction and its applications were compiled in
dependency order during development. Of 562 inherited objects, 542 match
earlier published object hashes. The other 20 are identified by source
revision and their object hashes are recorded here. The final
[exact input](ExactAudit.lean) checks ten statements against the original
definitions and the [audit output](20.log) gives 39 transitive axiom reports
using only propext, Classical.choice and Quot.sound.

Run `python tools/verify_hard_budget.py` from the repository root for the
statement digest, Lake build and kernel audit.
