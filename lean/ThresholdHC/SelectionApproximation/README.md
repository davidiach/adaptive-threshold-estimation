# Entropy perturbation and state compression

These are two formal components of the
[finite-law approximation scheme](../../../research/2026-11-06-selection-approximation/NOTE.md).
The full FPTAS, its bit complexity, and Python execution are not formalized here.
The [native audit record](../../../results/selection-approximation-20261106/README.md)
identifies the checked sources and transitive axioms.

## Locked definitions and targets

[Model.lean](Model.lean) was compiled and its
[specification lock](SPECIFICATION.json) recorded before writing the proofs.
The lock includes the existing cost entropy, finite-trace enumeration and
maximum-saving compression definitions, plus the Lean and package pins.

`Close c x y` means `x <= c*y` and `y <= c*x`. It handles zero without division.
For nonnegative finite vectors, `costTotal` is the sum and `costEntropy` is
the project's existing homogeneous entropy
`G(a) = A + sum_(a_i>0) a_i log(A/a_i)`.

| Target | Proof | Meaning |
|---|---|---|
| `EntropyPerturbationStatement` | [entropy_perturbation](Entropy.lean) | If both total costs lie in `[r,U]`, `r>0`, the two summaries have certified additive error at most `delta*A`, and both coordinates are `Close (1+eta)`, then `G(b) <= G(a) + (2*L*eta + delta*(1+eta))*A(a)`. Assumptions include nonnegative costs, `L,delta,eta >= 0`, `3+log(U/r) <= L`, and `0 <= Ha <= L*A(a)`. |
| `CompressionInvariantStatement` | [compression_invariant](Compression.lean) | For any finite list of menus and certified bin map with factor `c>=1`, every feasible trace has a retained feasible trace with at least as much saving and both nonnegative additive summaries within factor `c^m`. |

The entropy proof is about the actual entropy, not an assumed comparison
between abstract summaries. It proves the identity
`G(a) = A*(2+log(A)-log(r)) - sum_i a_i*(1+log(a_i/r))`,
the derivative bound on `[r,U]`, and the finite-sum bounds obtained by rounding
each positive logarithm upward. `entropy_relative` gives
`G(b) <= (1+epsilon/2)*G(a)` when `delta=epsilon/8`, `L*eta<=epsilon/8`,
`0<=eta<=1`, and `epsilon>=0`, with the other perturbation hypotheses.
`entropy_zero_of_close` covers the zero-total case separately and exactly.

The compression proof inducts through `trimSolve`, which actually extends
retained traces and keeps a trace with maximal saving in each pair of bins.
It reuses the project's existing finite `compress` operation. Thus the
conclusion supplies a feasible witness, not just a bound between hypothetical
states. Menus are processed from the tail of the list, as in the existing
`enumerate`; reversing a desired processing order gives the prototype's order.
Savings may be arbitrary reals; the two compressed coordinates must be
nonnegative.

## Bin certificates and remaining boundary

`ValidBins c key` requires equal keys on nonnegative inputs to imply `Close c`.
`validBins_of_intervals` derives this from a separate zero key, certified
positive intervals, and the upper/lower endpoint ratio bound.
`dyadic_cell_close` proves the ratio `1+1/M` for every cell
`[scale*(1+j/M), scale*(1+(j+1)/M)]`, for `scale,M>0` and `j>=0`.
The audit also instantiates this at `scale=1, M=2, j=0` with distinct endpoints,
and checks the concrete identity bin map.

The executable bin-index function has not been connected to those certificates.
Nor have the finite-law menu bridge, parameter choice, state count, rational
endpoint evaluation and final `(1+epsilon)` guarantee been assembled in Lean.
Those parts retain the paper-proof status in the research note. No new
statistical-risk theorem, exact polynomial-time optimizer, independent review,
or CI pass is claimed.

## Reproduce

After the repository's [pinned setup](../../../docs/VERIFY.md#setup), run
from the repository root:

```sh
python tools/verify_selection_approximation.py
python -m unittest discover -s tools -p 'test_selection_approximation.py' -v
python tools/verify_lean_sources.py
python tools/freeze.py --verify
```

The verifier accepts `--lean-exe PATH` and `--package-cache PATH` for an existing
native compiler and package cache. It checks the compiler version and each
external checkout's pinned revision and tracked-source cleanliness. External
compiled caches and the Lean distribution remain trusted inputs. All six local
modules are rebuilt into a fresh `.runtime/selection-lean/` directory; no local
project objects are reused. The two exact locked targets are checked and every
new public declaration receives a transitive-axiom report. Builds with warnings,
missing reports or nonstandard axioms fail. Logs, exact audit source, compiler
identity, source hashes and object hashes are retained with the result.
