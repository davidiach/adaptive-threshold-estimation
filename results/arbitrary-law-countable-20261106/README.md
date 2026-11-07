# Countable entropy transport: native Lean audit

Proof checkpoint: `0f3618e57e844005a61ed09a8ff1403e019d491b`.
Base checkpoint: `12965b08cf2c2daa2477466c34321c17de94f994`, the main-branch
merge of PR #73 after all five CI jobs passed.

The [record](status.json) binds all 45 project sources in this dependency
closure, three fresh serial native compilations with empty logs, and 42
compiled dependencies matching previously published hashes. No inherited
artifact is first identified here. The compiler, dependency manifests and
audit tools are included in the record.

All 16 independently restated exact statements and 16 transitive axiom
reports pass with only `propext`, `Classical.choice`, and `Quot.sound`.
The [audit input](arbitrary_law_countable.lean),
[reports](arbitrary_law_countable.log) and empty compilation logs are preserved.

## Checked scope

Finite-prefix entropy is continuous. Consequently, a uniform bound on its
extended-valued supremum passes to a coordinatewise limit. Entropy also
decreases under finite partial merging, including discarded cells, and
square partial sums converge to the sum of a summable array.

These facts extend the geometric factor-three transport inequality to
countably many source bands and displacements. The destination map is
arbitrary. Each destination column must be summable, but neither the full
inverse-square cost nor the full entropy needs to be finite. The extended
entropy is identified with canonical Gamma for every finite gap measure.
A supplied band-cell decomposition therefore gives
`Gamma(new) <= 3 Gamma(old)`.

The band-cell decomposition, row bounds, contraction bounds and local
summability are explicit premises. Constructing them from an increasing-gap
coupling remains to be formalized, as do the transported selections and the
remaining statistical adaptation argument. This is not a proof of the full
arbitrary-law oracle-adaptation theorem or of Python execution.
See the [current scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

## Replay

With the pinned Lean toolchain and Mathlib cache:

~~~sh
python tools/verify_arbitrary_law_countable.py
~~~

The proof-source guard checks 1,127 project Lean files. Frozen-source,
whitespace and relative-link checks pass. GitHub CI is separate and must be
reported for its actual checked commit.
