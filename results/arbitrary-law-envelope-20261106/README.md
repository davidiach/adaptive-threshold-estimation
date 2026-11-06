# Conservative finite CDF envelope: native Lean audit

Proof checkpoint: `9108a6e4909e2792940ad88c27e9196b4dc11eaf`.
The [record](status.json) identifies the sole project source, its fresh serial
native compilation with an empty log, compiler, dependency manifests, and
audit tools. There are no reused project objects in this dependency closure.

All 25 independently restated exact statements and 24 transitive axiom reports
pass with only `propext`, `Classical.choice`, and `Quot.sound`.
The [input](arbitrary_law_envelope.lean) and [reports](arbitrary_law_envelope.log)
are preserved with the empty compilation log.

Lean constructs a finite probability measure, proves its exact unresolved
zero mass and closed-CDF values at positive atoms, and proves CDF domination
from finitely many valid grid upper bounds. Taking prefix minima preserves
those bounds. The statistical pilot event supplying the bounds is not proved
by this component. Neither the complete adaptation theorem nor Python
execution is covered. See the [formal scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

Replay with the pinned toolchain and Mathlib cache:

~~~sh
python tools/verify_arbitrary_law_envelope.py
~~~

Frozen-source and whitespace checks passed. CI is reported separately for
the exact commit it checked.
