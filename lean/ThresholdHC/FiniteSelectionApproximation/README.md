# Assembled finite-law approximation

Start with [Specification.lean](Specification.lean) and the theorem
`finite_law_approximation` in [Full.lean](Full.lean). The
[scope guide](../../../docs/FINITE_SELECTION_APPROXIMATION.md) gives the
assumptions, constants, output certificate and execution boundary.

| Modules | Role |
|---|---|
| Bins | Concrete zero/dyadic-cell key, valid-bin proof and rational-key equivalence |
| Parameters | Input-derived `L`, `M`, logarithmic rounding, accumulated error and `beta` |
| Traces, Compression | Cost range, certified summaries and original-entropy comparison |
| States, Frontier | Every-stage `S` bound and candidate-extension count |
| Menus, Objective | Actual finite gap-law menus, `Q=n+m`, original `K` and positive floor |
| Endpoints | Rational endpoint specification, refinement termination and certificate chain |
| Specification, Full | Single assembled theorem, including the witness and all bounds |

The theorem covers all finitely supported laws, including rational finite
inputs. Bit complexity and numerical/Python execution remain outside the
formal claim. Run `python tools/verify_finite_selection_approximation.py` from
the repository root. It checks the new [lock](SPECIFICATION.json), independently
restates the conclusions, and audits every declaration's transitive axioms.
