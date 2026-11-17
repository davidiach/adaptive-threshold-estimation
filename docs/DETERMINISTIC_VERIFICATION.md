# Deterministic toolkit verification

Issue [#85](https://github.com/davidiach/adaptive-threshold-estimation/issues/85)
extends verification to actual numerical outputs. The first implemented boundary
is an opt-in certificate path for `sqrt_interval`, `log_interval`, and
`cost_entropy` in the exact toolkit. It does not close #85.

The [Lean checker](../lean/ThresholdHC/DeterministicCertificates/Checker.lean)
has a universal soundness theorem for every input expression and proposed
certificate. The [Python adapter](../toolkit/threshold_toolkit/deterministic_certificates.py)
calls the existing numerical routines and emits a closed Lean theorem about
the caller's exact inputs and the returned rational endpoints. Acceptance
requires Lean to check that theorem. The
[entropy bridge](../lean/ThresholdHC/DeterministicCertificates/Entropy.lean)
identifies its expression with the existing, unchanged
[`EntropyTailQuantile.costEntropy`](../lean/ThresholdHC/EntropyTailQuantile/CostEntropy.lean).
The original numerical routines and their sealed research package are unchanged.
The [clean-checkpoint evidence](../results/deterministic-certificates-20261117/README.md)
records the exact statements, actual outputs, rejection cases and whole-project audit.

## Contract and execution boundary

For an accepted interval `[l,u]`, the generated theorem states `l ≤ f(x) ≤ u`
over the reals. For square roots it also proves

`u-l ≤ 2^(-bits) * min(1, sqrt(x))`.

The entropy theorem covers every finite nonnegative rational vector, including
empty vectors and zero coordinates. Its target is `A + sum a_i log(A/a_i)`
with the existing continuous-at-zero convention. It certifies the numerical
functional, not statistical risk or a confidence interval.

The checker supports rational constants, addition, scaling with either sign,
minimum, maximum, square root and logarithm. It checks every child interval.
Square-root endpoints are verified by nonnegativity and squared inequalities.
Logarithms use a finite rational atanh sum, a proved geometric remainder,
binary range reduction with an integer exponent, and monotonicity. The
checker uses Mathlib's independently proved, looser remainder; the producer
offers eight extra terms to fit it within the legacy output. If the witness
does not fit, verification fails. No theorem assumes this producer strategy
will always succeed. The checker is structurally recursive and terminating.

`accepted_sound` additionally requires that the externally claimed interval
equals the checked root interval. `proof_source` builds the target from the
caller's `Request`; certificate metadata must match that request, including
precision. Only bounded exact rational data are interpolated into Lean.
Certificate fields cannot supply imports, tactics, declarations or raw code.
The concrete proof uses `norm_num`, whose proof terms are checked by the kernel;
it does not use `native_decide`, a trusted Python Boolean, or a checksum as proof.

This is certificate checking, not a semantics or refinement proof for CPython.
The trusted execution boundary includes the adapter's input/output binding and
source generation, Python/Fraction and process execution, the pinned Lean
compiler/kernel, Mathlib and the imported compiled cache, and the operating
system. The generated source exposes the entire concrete theorem for independent
inspection/rechecking. The focused audit pins source identities, checks exact
types and transitive axioms, and replays all four new project modules through
the independent kernel checker. The reused external compiled cache remains
trusted; replay of every imported Mathlib module is not claimed.

Calling a legacy function, `produce`, or `proof_source` alone does not produce
a verified result. `verify` raises `VerificationError` unless the kernel succeeds
and reports the expected closed theorems with only `propext`, `Classical.choice`
and `Quot.sound`. A current build of the audited project must be supplied as
`lean_dir`; an arbitrary same-named project is not an interchangeable trust root.

## Supported input and failure behavior

`Request` takes `sqrt`, `log`, or `entropy` and a tuple of exact integers,
Fractions, or integer/fraction strings. Floats and booleans are rejected.
Square roots require one nonnegative argument; logarithms one strictly positive
argument; entropy up to sixteen nonnegative coordinates. Decimal strings
accepted by some legacy APIs are deliberately outside this narrower certificate
interface: use their exact fraction representation.

The numerical precision ranges remain `16 ≤ bits ≤ 512` and
`4 ≤ log_terms ≤ 256`. Resource limits are 2,048 bits per input numerator and
denominator, 8,192 bits per encoded rational intermediate/endpoint, and two
million UTF-8 bytes of generated source. Proof reduction has finite heartbeat
and recursion limits. Kernel execution defaults to 120 seconds, configurable
up to 600 seconds. Out-of-domain data, mismatched requests, unknown fields,
reversed intervals, failed inequalities, unavailable Lean and exhausted
resources all fail without a verified result. These are explicit verification
limits, not impossibility claims about the mathematical problem.

An accepted log/entropy certificate guarantees enclosure. It does not assert
a prescribed relative width for these functions. The square-root width is
separately checked, including zero, exact squares and tiny positive arguments.
Arithmetic is exact rational arithmetic. This work makes no polynomial bit-cost
claim and no universal completeness or termination-time claim for the producer
plus Lean elaborator on all legacy inputs.

## Use and reproduction

From the repository root, with the pinned Lean toolchain available:

```text
cd lean
lake build ThresholdHC.DeterministicCertificates.Entropy
cd ..
python tools/verify_deterministic_certificates.py --no-build
python -m unittest discover -s tools -p test_deterministic_certificates_audit.py -v
```

With the toolkit installed (or `toolkit/` on `PYTHONPATH`):

```python
from fractions import Fraction
from pathlib import Path
from threshold_toolkit.deterministic_certificates import Request, produce, verify

request = Request("sqrt", (Fraction(3, 10**80),))
certificate = produce(request)  # actual legacy output, still untrusted
checked = verify(request, certificate, lean_dir=Path("lean"))
print(checked["output"])
```

The audit writes to a fresh `.runtime/deterministic-certificates/` directory.
It records eight independently restated exact statements, all declared roots,
four-module kernel replay, eight actual-output proofs and four rejected
certificates, source hashes and the toolchain identity. Examples include zero,
tiny nonsquare input, an exact square, a logarithm below one, the default
32-term logarithm, empty/all-zero entropy and mixed zero/positive entropy.
Adversarial cases include a false root, a valid but over-wide square-root
enclosure, a wrong logarithm and a wrong entropy interval. Rejection evidence
must reduce a proposed numerical check to `False`; a timeout is not counted
as a successful negative test.

The unit tests separately exercise request substitution, precision substitution,
type confusion, code injection, invalid domains, missing/forbidden axiom reports,
missing kernels and resource failures. These tests are regression evidence.
Universal soundness comes from the Lean theorems. A finite sample pass does
not establish that every legacy output is accepted.

## Deterministic API inventory

The table inventories the public deterministic surfaces at integrated main
`2e8e8b5e2a06a39f83db41376317f705789f9e0f`. Public record types include their
deterministic properties/serialization methods. Numerical helpers used only
inside stochastic execution are included where they affect certificates;
coin callbacks, sampling, simulation and controller execution belong to #86.
“Pending” means the implementation-to-specification connection is still open,
even where a mathematical theorem or extensive tests already exist.

| Surface and public entry points | Domain, result and failure contract | Verification connection |
|---|---|---|
| [Exact primitives](../toolkit/threshold_toolkit/rare_event_functional.py): `rational`, `Interval`, `Precision`, `sqrt_interval`, `log_interval`, `cost_entropy` | Exact arithmetic; parser accepts int/Fraction/decimal or rational strings up to 16,384 input bits. Ordered Fraction endpoints. Precision ranges as above. Sqrt input nonnegative, log positive, costs nonnegative. Invalid types/domains raise. | New opt-in checker verifies actual sqrt/log/entropy outputs and sqrt width on its bounded domain. The general Python parser/interval class is not refined. |
| Exact finite laws: `Atom`, `FiniteGapLaw`, `band_index` | Positive rational atoms in `(0,1/2]`, positive masses summing exactly to one; duplicates merged and sorted. Band convention `(2^(-j-2),2^(-j-1)]`. Zero-gap atoms rejected. | Pending: canonicalization, probability identity and exact endpoint/band labels. |
| Exact functional: `evaluate_selection`, `quantile_split`, `quantile_certificate`, `transfer_enclosure`, `RoundedLaw`, `round_up_within_bands` | `rho in (0,1/4]`, positive budget, one selected fraction in `[0,1]` per canonical atom. Capped feasible objective, fractional quantile boundary, or transfer/rounding bounds. These are deterministic rate quantities. | Primitive checker available; finite sum/measure and objective bridge, quantile mass identity, transfers and rounding of actual outputs pending. |
| Suffix enumeration: `suffix_search_size`, `exhaustive_certificate`, `threshold_certificate`, `verify_certificate` | Finite exact laws; exhaustive suffix product with an explicit search limit; threshold search is a restricted family. Legacy verification rebuilds the Python record. | Pending: certified completeness of the enumerated menu and connection of global lower bounds to original `K`. Rebuilding a record alone is not this new kernel check. |
| [Band costs](../toolkit/threshold_toolkit/band_cost_selection.py): `SelectionResult`, `select_by_band_cost` | Exact suffix options and cost-multiset states; rational comparison of savings of the form `x+y/sqrt(B)`; interval objective and optional separated optimizer. A transition cap raises on exhaustion. | Mathematical DP and gap-law bridges exist. Actual state generation, comparison, pruning and returned certificate remain pending. |
| [Approximation](../toolkit/threshold_toolkit/approximate_selection.py): `ApproximateSelectionResult`, `select_approximately` | Finite laws and `epsilon in (0,1]`; two rounded summaries, entropy/log enclosures and refinement stopping inequality. State/transition and finite precision limits can raise. | #93's finite-law theorem is merged through #121. Actual rounded-log keys, retained states and stopping endpoints are not yet connected to it. Operation count and polynomial bit complexity are distinct. |
| [Integration oracles](../toolkit/threshold_toolkit/known_law_oracle.py): `SplitIntegrals`, `KnownGapOracle`, `FiniteGapOracle` with `null_prefix`, `split`, resolved-error and tail-work callbacks | Finite rational polynomial null likelihoods; quantile core, band costs, unresolved mass and inverse-gap tail; log upper bounds in tail work. External protocol callbacks promise bounds but may be arbitrary code. | Pending: finite sum identities, direction of each returned bound, fractional boundary atoms and truthful external-oracle premises. |
| [Known-law plan](../toolkit/threshold_toolkit/known_rare_estimator.py): `cap_limit`, `Level`, `RarePlan`, `plan_known_rare` | Positive budget, `rho in (0,1/4]`, nonnegative oracle bounds and valid bands; cap search, level prices, allocation, squared-error certificate and constant fallback. Reaching the cap-search limit returns the constant. | Pending: actual prices/rounding and allocations. #81's checked planner uses different conservative prices; its theorem does not verify these Python constants. |
| [Gap envelope](../toolkit/threshold_toolkit/gap_envelope.py): `GapEnvelope`, `EnvelopePlan`, `plan_gap_envelope` | Decreasing rational CDF bounds starting at one; dyadic positive atoms plus residual zero mass; positive-part normalization, fair null-prefix mass at zero, constant branch when zero mass is at least rho. Planning uses positive depth, `rho in (0,1/4]`, `delta in (0,1)`. | Pending: construction, split and exact finite-oracle connection. Actual domination of a true law is a separate statistical premise, not implied by constructor validation. |
| [Finite-family pilot](../toolkit/threshold_toolkit/law_identification.py): `LawPilotPlan`, `plan_law_pilot` | Nonempty distinct candidate finite laws, `delta in (0,1)`, positive moment limit; exact even moments and separation/count/cap arithmetic. Raises if the finite moment limit does not separate candidates. | Pending deterministic plan refinement; sampled identification belongs to #86. |
| [Tail plan](../toolkit/threshold_toolkit/tail_mass.py): `TailMassPlan`, `plan_tail_mass` | Positive integer depth, `delta in (0,1)`; scales, thresholds, block and flip caps. | Pending deterministic schedule arithmetic; statistical capped probes and their runtime remain separate. |
| [Budget ladder](../toolkit/threshold_toolkit/budget_ladders.py): `Stage`, `stage`, `plan`, `schedule_record`, `verify_schedule` | Bounded integer indices/budgets, nonnegative authorized cumulative budget, exact powers and caps. Record verifier checks structure and parameter binding by recomputation. | Pending kernel-checked schedule/record connection. Physical execution and increasing-budget state belong to #86. |
| [Median schedule](../toolkit/threshold_toolkit/confidence_amplification.py): `median_block_count`, `MedianSchedule`, `verify_schedule_record` | `delta,rho in (0,1/4]`, positive integer budget; odd count, exact squared-tail comparison, physical cap. Raises when the count exceeds `max_blocks`. | Pending actual count/cap refinement. Conditional median mathematics is already checked; record equality is not its execution proof. |
| [Confidence arithmetic](../toolkit/threshold_toolkit/confidence_ladders.py): `stage_delta`, `ClosedInterval`, `bernoulli_interval` | Rational stage allowances, interval intersection/midpoint; integers `0 <= heads <= flips`, positive flips, `delta,upper in (0,1]` for Bernoulli intervals. Empty intervals have no midpoint. Private sqrt/log helpers use finite approximations. | Pending enclosure direction and schedule connection; statistical coverage additionally needs the appropriate observation model. |
| [Floating rare-event API](../toolkit/threshold_toolkit/rare_events.py): `FiniteGapLaw`, `EntropyBand`, `RareEventEvaluation`, `RateBudget`, `RareEventProfile.evaluate/rate/budget_for_rate` | Finite binary floats, positive gaps/masses, normalization and log-domain calculations; finite target/budget validation. Inversion returns numerical estimates, with overflow represented by infinity and a finite log-budget where available. | Pending floating-error and inversion certificates. These are not rational outward enclosures. An infinite float is not an impossibility theorem. |
| [Floating planning](../toolkit/threshold_toolkit/planner.py): `Population`, `GuessedRates`, `EvenlySpread`, `difficulty`, `floor_budget`, `binomial_tail`, `MajorityPlan`, `majority_plan_for_budget/target`, `score_blocks`, `rms_upper_bound`, `BudgetPlan`, `TargetPlan`, `plan_budget/target` | Validated population/rate inputs and positive finite targets/budgets; NumPy/SciPy calculations, bounded search and an odd grid growing by 1.25. The search result applies to the tested grid and configured limits. | Pending floating precision, supported-domain search and actual output bounds. Monte Carlo `simulate` is execution evidence, not a certificate. |
| [Estimator helpers](../toolkit/threshold_toolkit/estimator.py): `level_probability`, `threshold`, `budget_level` | Floating level probabilities and prefix thresholds; intended integer levels and `1 <= n <= cap`. Those two helpers do not comprehensively validate the intended domain. `budget_level` rejects nonfinite budgets or budgets below four. | Pending deterministic helper refinement; PRNG, flips, freshness and stopping behavior are #86. |

The stochastic wrappers `known_law_interval`, `arbitrary_law_interval`,
`unknown_law_confidence`, and `FiniteFamilyConfidenceLadder` also contain
deterministic setup: radius `sqrt(8*MSE)` rounded upward, fallback intervals,
pilot-depth selection, and budget/failure splits. These inherit the pending
planner/schedule contracts above; their integrated generator execution remains
#86. `rare_event_cli.py` and `__main__.py` expose the floating calculators and
planning APIs through argument parsing; they do not add a certificate boundary.

The top-level package exports the floating `FiniteGapLaw` and `RareEventProfile`.
The exact law and new certificate adapter require their explicit module imports;
the two `FiniteGapLaw` classes are not interchangeable.

## Remaining order for #85

1. Connect canonical finite laws, exact band boundaries and quantile fractions to
   the measure definitions. Use those identities to certify an actual feasible
   objective and every finite-oracle integral, including residual zero mass.
2. Certify global selection: menu completeness, DP transitions and dominance,
   approximate bins/rounding, termination or explicit limits, and the final
   original-`K` endpoint chain. The proved abstract algorithm in #93 is the
   target, not evidence that the Python search already implements it.
3. Connect concrete planner prices, allocations, cap/fallback decisions and
   schedules. Carry external-oracle assumptions explicitly. Resolve the known
   difference between mathematical and toolkit level prices before transferring
   a statistical guarantee.
4. Give the floating public calculators sound rounding/search contracts or
   route them through a proved checker; preserve diagnostic-only APIs as such.

The core mathematical theorem and publication remain complete. These are
extensions of the deterministic implementation boundary; stochastic refinement,
unrestricted exact-selection complexity and sharp finite-cap convergence remain
separate issues #86, #87 and #88.
