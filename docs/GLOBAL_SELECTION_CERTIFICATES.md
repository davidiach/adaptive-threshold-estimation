# Global selection output certificates

Issue [#85](https://github.com/davidiach/adaptive-threshold-estimation/issues/85)
now has an opt-in kernel checker for bounded outputs from
`exhaustive_certificate`, `select_by_band_cost`, and `select_approximately`.
The [adapter](../toolkit/threshold_toolkit/global_selection_certificates.py)
calls these unchanged producers and checks their global interval, returned
selection, complete suffix count, DP optimality claim when true, and
approximation guarantee. This extends the
[finite-law objective checker](FINITE_LAW_CERTIFICATES.md) from feasible upper
bounds to lower bounds on the original optimization problem.

## What an accepted certificate establishes

For the caller's exact finite probability law, `0 < rho <= 1/4`, and `B > 0`,
write `K` for the existing `EntropyTail.selection` over **all submeasures** and
`J(s)` for the capped objective of a hard selection. Acceptance proves

`lower <= K <= J(s) <= upper`.

The [menu bridge](../lean/ThresholdHC/GlobalSelectionCertificates/Menu.lean)
identifies the actual support of the atomic measure, applies the existing
bandwise-suffix attainment theorem, and identifies the objective with the
rational expression checked by the numerical kernel. The supplied menu must
be complete, contain only suffixes, have no duplicates, and have exactly the
reported suffix count. Those conditions are kernel obligations. A missing
candidate cannot silently raise the global lower bound.

Every menu candidate receives a checked objective lower bound. The actual
returned selection is checked to be a suffix and receives a checked upper bound.
For exhaustive search's
saturated output, the legacy `None` witness is preserved; the proof uses the
empty selection internally to establish the upper bound and does not report
it as a producer-returned witness.

For DP, `optimality_proved=True` additionally requires `J(s)=K`. A false flag
does not assert nonoptimality. For approximation, the checker proves the
returned witness interval, `lower > 0`, the equality of the output epsilon to
the requested epsilon, `upper <= (1+epsilon)*lower`, and
`J(s) <= (1+epsilon)*K`. These are bounds on the deterministic rate functional,
not statistical risk or confidence coverage.

The [pruning primitives](../lean/ThresholdHC/GlobalSelectionCertificates/Trace.lean)
also prove that an accepted finite pruning stage retains only candidate states,
has unique keys, and supplies a same-key representative with at least as much
`f+t/sqrt(B)` for the supplied rational savings coordinates of every candidate.
Rational squared comparisons
are connected to the real expression involving `sqrt(B)`, including equality
and either sign of the difference. Equality of the existing rational dyadic
bin keys implies the existing multiplicative closeness relation. These
generic primitives are audited separately; the adapter does **not** yet bind
a full internal DP transcript to the producer's execution or state counters.

## Interface and limits

```python
from fractions import Fraction as F
from pathlib import Path
from threshold_toolkit.global_selection_certificates import Request, produce, verify

request = Request("approximate", ((F(1, 4), F(1, 2)), (F(1, 2), F(1, 2))),
                  budget=F(1024), epsilon=F(1, 10))
certificate = produce(request)  # untrusted output and menu witness
checked = verify(request, certificate, lean_dir=Path("lean"))
```

Requests support one to six distinct increasing positive gaps at most `1/2`,
positive rational masses summing to one, and the existing precision and exact
rational size limits. There are at most 64 suffixes. The producer work cap is
an exact integer from 1 to 4096. Verification additionally has a two-million-byte
source limit, bounded proof reduction, and a timeout of at most 600 seconds.
Only exact bounded data enter generated source; certificates cannot supply
Lean commands, imports or proof text.

The adapter checks a documented projection of the producer's output. Internal
frontier counts, transition counts, peak sizes, approximation parameter
construction, and precision-refinement history are not certified output fields.
The returned verification record explicitly marks internal execution and
polynomial verification cost as unverified. The checker enumerates the complete
suffix family even when certifying a DP or approximation output; no efficient
certificate-checking or bit-complexity theorem follows from this implementation.

Internal numerical witnesses use stronger precision to fit the producer's
endpoints. Some correct outputs, including unresolved exact ties, may not admit
a proof from this generator within its limits. Source generation, parser success,
and producer success never imply verification. Kernel failure, unavailable
Lean, unsupported data and resource exhaustion all raise an error.

As in the previous certificate layers, the trusted execution boundary includes
input/output binding and source generation, Python/Fraction and subprocess
execution, the pinned Lean kernel, the imported compiled cache, and the operating
system. This is output certification rather than a CPython refinement proof.
The existing producers and every previously frozen proof remain unchanged.

## Verification and remaining work

Run `python tools/verify_global_selection_certificates.py` for the focused
exact-type, transitive-axiom, independent kernel-replay and concrete-output audit.
Its source snapshot covers all transitive project dependencies, the adapter,
tests, audit tools and producer modules. The audit also exercises false global
bounds, wrong witnesses and epsilon, incomplete or duplicate menus, and incorrect
suffix counts. Unit and audit-guard tests are in the normal toolkit and tools
test suites. The [published record](../results/global-selection-certificates-20261117/README.md)
identifies the source checkpoint and exact checks actually performed.

#85 remains open for complete internal solver transcripts and complexity
accounting, the other selection entry points, concrete planner/schedule outputs,
and floating calculators. Python/PRNG execution refinement remains separately
tracked in #86.
