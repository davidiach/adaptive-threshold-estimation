# Strictness of the sharp RMS bound: library audit

Theorem `sharp-rms` of v6 Appendix AA gives $R_\mu(B)\ge\omega_\mu(B^{-1/2})/6$
for every gap law and every $B\ge1$, with equality at $\mu=\delta_{1/2}$ and
$B=4$; it is Lean-checked in
[`SharpRMS`](../../lean/ThresholdHC/SharpRMS/Full.lean). The remark after it,
that equality requires $B=4$ because every case of the proof is strict for
$B\ne4$, had a paper proof only. Lean now checks it, in
[`lean/ThresholdHC/SharpStrict`](../../lean/ThresholdHC/SharpStrict/Full.lean).
The `SharpRMS` group and its record are unchanged. The audit runs below were
made at commit
[`1e76c11`](https://github.com/davidiach/adaptive-threshold-estimation/commit/1e76c11).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/SharpStrict/Specification.lean)
states six targets, in the model, risk and modulus of `SharpRMS`.

| Target | Statement |
|---|---|
| `strict_sharp_lower` | For every gap law and every $B\ge1$ with $B\ne4$: $\omega_\mu(B^{-1/2})/6<R_\mu(B)$. |
| `strict_coefficient` | For each such $B$, one coefficient $c>1/6$ gives $R_\mu(B)\ge c\,\omega_\mu(B^{-1/2})$ for every law. |
| `sharp_equality_case` | $R_\mu(B)=\omega_\mu(B^{-1/2})/6$ with $B\ge1$ forces $B=4$. |
| `small_budget_lower` | For $0\le B\le4$ and every law: $R_\mu(B)\ge\sqrt{(10-B)/216}$, which exceeds $1/6$ exactly when $B<4$. |
| `critical_strict` | Every point mass $\delta_g$ with $2g<1$, at its critical budget $(2g)^2B=4$, has $R>1/6$. |
| `oracle_strict_sharp_lower` | The strict bound with every magnitude revealed, and with each fresh magnitude selected. |

## How the proofs go

The proofs are in [`Strict.lean`](../../lean/ThresholdHC/SharpStrict/Strict.lean).
They follow the cases of the `SharpRMS` proof and keep the slack that the
original statements drop.

- **$B<4$.** The small-budget Bayes argument of `SharpRMS`, with work at most
  $B$ instead of $4$, gives the prefix Bayes risk $(10-B)/216$ instead of
  $1/36$, so $R_\mu(B)\ge\sqrt{(10-B)/216}>1/6\ge\omega/6$ for every law,
  since $\omega\le1$. The paper argues here by the revealed-sign Fisher bound,
  which gives the larger $\sqrt{1/(6(2+B))}$; the constant
  $\sqrt{(10-B)/216}$ is the Lean route's, not the paper's.
- **$B>4$.** The gap reduction gives $R_\mu(B)\ge\omega\cdot R_{\delta_g}(B)$
  at $g=B^{-1/2}$, and $\omega>0$, so it suffices that the critical point mass
  has risk above $1/6$. For $B\ge25$ the large-budget coefficient
  $\sqrt{59/2100}>1/6$ applies. For $4<B<25$ the information-price integral
  is strictly below its cap $2/3$: on the window $2/5<2g\le39/40$ the existing
  certified chain contains an interval with lower end below $40960\cdot2g$,
  which rescales the certified upper sum strictly below $2/3$; for
  $39/40\le2g<1$ the near-perfect envelope integrates to
  $2/3-(1-s^2)(477/5120-11/(192s^2))<2/3$. The existing window certificate
  is reused; the only new kernel reduction is a `rfl` walk of its list of 140
  interval endpoints.
- **Oracles.** The oracle lower bounds of `SharpRMS` reduce to one gap with
  $g=\min\{1/2,B^{-1/2}\}$, so the same strict cases apply. The remark itself
  speaks of the ordinary model; the oracle form follows from the same cases.

Several helpers of `SharpRMS` that are private or fixed to the constant
$1/6$ are copied into this group. A reviewer diffed each copy against its
original: the copies either match it byte for byte or change only the
constant.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_sharp_strict.py --replay --jobs 3` | 9 exact statements (the 6 targets and 3 components) and 29 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [sharp-strict-audit.log](sharp-strict-audit.log) |
| `python -m unittest discover -s tools -p 'test_sharp_strict.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,234 constants (13,842 theorems) in 1,480 modules, same axioms. 147 exported instances. 3,252 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,481 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
fifteen entries to `tools/definition_lock.json`: the six statements and the
private helpers `flatPrior`, `box`, `histogram`, `cappedGap` and
`lastEndpoint` with the declarations Lean generates for it. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. For $4<B<25$ the coefficient above $1/6$ is
existential; it is explicit for $B<4$ and $B\ge25$. The transitive closure
contains the existing `decide +kernel` window certificates of `SharpRMS`.

## Review

Before the specification was pinned, two reviewers that had not written the
proofs read the group. One compared the statements with the remark: they say
that the bound holds and that equality forces $B=4$, the strict inequality
has content (the risk is at most one and the modulus is positive), and the
equality case is attained at $\delta_{1/2}$, $B=4$. The other diffed the
copied helpers against `SharpRMS`, checked each case of the proof and the
reuse of the window certificate, and printed the axioms. Neither found a
blocking problem; their wording fixes were applied. These were reviews by AI
agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
