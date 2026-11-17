# Finite-law relative approximation

The [assembled theorem](../lean/ThresholdHC/FiniteSelectionApproximation/Full.lean),
`finite_law_approximation`, gives a bandwise upper-gap suffix witness and rational
endpoints enclosing the original capped entropy-tail functional `K`. Its
[specification](../lean/ThresholdHC/FiniteSelectionApproximation/Specification.lean)
allows every finitely supported probability law on `(0,1/2]`, hence every
rational finite law, with `0 < rho <= 1/4`, `B > 0`, and `0 < epsilon <= 1`.
There are no supplied bin, logarithm, entropy-error or positive-floor premises.

With `beta = 1+epsilon/4`, the output satisfies

`0 < l`, `l/beta <= K <= J(witness) <= u <= (1+epsilon)*l/beta`.

Here `J` is the original capped objective of the selected submeasure. The
definition of `K` compares against **all fractional submeasures**, not just the
finite menu. The concrete suffix theorem supplies an exact optimum before
compression, and the retained feasible witness has objective at most `beta*K`.
The final witness minimizes the upper endpoint among retained states.

## Parameters, states and endpoint refinement

The input constructs one suffix menu per occupied band. Let `r` be the least
positive option cost, `U` the sum of the largest cost in each menu, `R=U/r`,
`m` the number of occupied bands, and `n` the number of support atoms. The proof
derives `r>0`, `R>=1`, `m>0`, and the presence of the empty option in every menu.
It uses

`L=4+ceil(log2 R)`, `M=ceil(16*m*L/epsilon)`, `delta=epsilon/8`.

The concrete bin key has a separate zero key and `M` equal subcells in every
dyadic interval. `rationalKey_cast` connects the rational integer-log/floor
formula to the real key; `binKey_valid` proves its factor `1+1/M`.
For each partial stage, the accumulated error `eta` satisfies
`0 <= eta <= 1` and `L*eta <= epsilon/8`. The rounded summary controls actual
cost entropy, including the zero-total case.

Every intermediate retained frontier has at most

`S = 1 + M^2*(1+floor(log2 R))*(1+floor(log2(L*R)))`

states. Completing partial traces by empty options puts them in the same
input-derived summary box. There are at most `Q=n+m` menu options in total,
so the number of candidate extensions before trimming is at most `Q*S`.
This counts extensions; it is not a count of arithmetic bit operations.

The positive floor for each original objective is

`d = min{rho, sqrt(rho*r/B), 1, 2/sqrt(B)} > 0`.

The formal endpoint specification rounds the original `J` to a rational grid
of width `1/(N+1)`. Refinement succeeds by
`N=ceil((beta+1)/((beta-1)*d))+1`. Thus termination is derived from a positive
floor, including the empty selection; it is not an additional assumption.

## Verification boundary

The [new audit](../tools/verify_finite_selection_approximation.py) checks 12
exact statements, including an independent restatement of the assembled
theorem with explicit `L`, `M`, `S` and `beta`, and transitive axiom reports for
all 93 declarations. Its new specification lock pins 79 specification,
dependency and toolchain files. The earlier
[component specification](../lean/ThresholdHC/SelectionApproximation/SPECIFICATION.json)
and historical evidence remain unchanged. See the
[proof record](../results/finite-selection-approximation-20261117/README.md)
for the audited checkpoint and source identities.

The theorem is about the mathematical finite scheme and certified endpoints.
`upperLog` and endpoint values use exact real logarithms and floor/ceiling in
their specification. Correct execution of numerical enclosures, menu
construction and the Python implementation remains in
[#85](https://github.com/davidiach/adaptive-threshold-estimation/issues/85).
The rational bin formula has an exact mathematical bridge; this does not
certify the whole Python program.

The [note's polynomial bit-complexity proof](../research/2026-11-06-selection-approximation/NOTE.md)
remains paper-only: no formal machine cost model is asserted. This result does
not resolve [#87](https://github.com/davidiach/adaptive-threshold-estimation/issues/87)'s
exact polynomial-time question or alter the statistical minimax theorem.
No historical record or published PDF is upgraded by this new proof record.

## Reproduce

After the [pinned setup](VERIFY.md#setup), run:

```sh
python tools/verify_finite_selection_approximation.py
python -m unittest discover -s tools -p 'test_finite_selection_approximation.py' -v
python tools/verify_lean_sources.py
python tools/verify_project_axioms.py
python tools/verify_locks.py
```

Each audit writes new evidence under `.runtime/finite-selection/`; an explicit
`--output-dir` must not exist. `--no-build` is only for a tree whose current
sources have already been built completely. Cached Mathlib objects and the
Lean distribution remain trusted inputs, as in the existing project audits.
