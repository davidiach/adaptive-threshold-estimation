# The eight-fifths quantile-selection comparison

For every probability law on $(0,1/2]$, $0<\rho\le1/4$ and $B>0$, Lean
proves $K\le Q\le(8/5)K$. It also proves $T_h\le K$ and the endpoint
$K=Q=\rho$ when $h\ge t$. A quantile atom can be split fractionally and
the full-law entropy can be infinite.

The [exact statements](https://github.com/davidiach/adaptive-threshold-estimation/blob/952803dd15c35219cf4069556a442b159d760a46/lean/ThresholdHC/QuantileSelection/Specification.lean)
precede the proof. The [completed theorem](https://github.com/davidiach/adaptive-threshold-estimation/blob/4916e389c6e2203998c274fa0f6a4854ae758042/lean/ThresholdHC/QuantileSelection/Full.lean)
uses both entropy inequalities in Lemma 1, the factor-two separated cost in
Lemma 2 and the previously checked scalar Lemma 3. Lemma 2 uses a geometric
reference distribution with mass $3/8$ in each of the two nearest bands.

The [verification record](status.json) binds the compiler, source files,
native artifacts, and hashes of the individual logs. The isolated native run
rebuilt 11 modules, including the scalar proof and
its specification. The other 55 project sources and
compiled inputs matched the [previous verified record](../entropy-tail-explicit-20261104/status.json).
The run used the pinned Mathlib cache. All 12 compiler commands passed.
The [final kernel input](ExactAudit.lean) checks four exact statements, including
the comparison for the selection functional used by the minimax theorem.
The [axiom reports](12.log) cover 20 declarations and use only
`propext`, `Classical.choice` and `Quot.sound`.

From the repository root run

```sh
python tools/verify_quantile_selection.py
```
