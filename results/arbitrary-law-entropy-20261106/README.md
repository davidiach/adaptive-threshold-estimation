# Finite arbitrary-law entropy transport: native Lean audit

Proof checkpoint: `b4512c844bc5e830c7a7d451792b911c3f655103`.
The [record](status.json) identifies the three-source project dependency
closure, two fresh serial native compilations with empty logs, and one reused
object matching the prior published audit. No inherited artifact is first
identified here. Dependency manifests and verifier sources are hashed.

All 15 independently restated exact statements and their transitive axiom
reports pass with only `propext`, `Classical.choice`, and `Quot.sound`.
The [audit input](arbitrary_law_entropy.lean) and
[reports](arbitrary_law_entropy.log) are preserved alongside the empty build logs.

The result is the finite rowwise entropy-transport inequality, support-sensitive
cross entropy, arbitrary finite merging, and the geometric code giving the
factor-three bound. It is not yet a countable measure-transport theorem or the
full arbitrary-law adaptive statistical result. See the
[current formalization scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

Replay with the pinned Lean toolchain and Mathlib cache:

~~~sh
python tools/verify_arbitrary_law_entropy.py
~~~

The source guard checked 1,122 project Lean files, and frozen-source and
whitespace checks passed at the proof checkpoint. GitHub CI is separate and
must be associated with the commit on which it ran.
