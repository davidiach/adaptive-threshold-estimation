# Observable learned-law stage: native Lean audit

Proof checkpoint: `dcadeff07529036f4ba9f55878cf470d1e0da6a6`.
The [record](status.json) binds the complete 644-source project closure,
one fresh serial native compilation with an empty log, and 643 unchanged
compiled dependencies matching previously published hashes. There are no
first-time inherited artifacts. The compiler, dependency manifests and
verification tools are also identified.

All 17 independently restated exact statements and 16 transitive axiom reports
pass with only `propext`, `Classical.choice`, and `Quot.sound`.
The [audit input](arbitrary_law_stage.lean), [reports](arbitrary_law_stage.log)
and empty compilation log are preserved here.

## Checked construction

The stage pays for a fixed pilot and computes a finite conservative-envelope
candidate from its actual observed word. The candidate is a probability measure
on every word; CDF domination follows when the finite grid bounds are valid.
It then selects a continuation using that learned law and runs it on disjoint,
untouched persistent coin labels. Its chronological readback equals the
table-level construction. Both interval endpoints share one purchase policy,
obey the unconditional cap `pilotCost + continuationCost`, and jointly have
the stated law in the original hidden-gap experiment. Gap-dependent measurable
sign distributions are allowed.

This is an execution component, with a supplied pilot, bound rule and
continuation. It does not instantiate the statistical pilot or robust
continuation, prove their probability or risk bounds, or establish the final
all-budget controller. Those conclusions are not assumed as premises to these
execution lemmas. Python execution is outside this verification claim.
See the [current scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

## Replay

With the pinned Lean toolchain and Mathlib cache:

~~~sh
python tools/verify_arbitrary_law_stage.py
~~~

All four new arbitrary-law modules have empty native compilation logs. The
combined three audits check 57 exact statements and 55 transitive reports.
The 23 existing source-guard and audit-validator regression tests pass,
the source guard checks all 1,124 project Lean files, frozen-source verification
passes, and relative-link and whitespace checks pass. GitHub CI is separate
and must be identified by its actual checked commit.
