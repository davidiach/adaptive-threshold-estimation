# RMS coefficient for budgets of at least 25: library audit

The Lean proofs that bracket the best RMS lower coefficient for budgets of at
least 25 came from the
[RMS constants research package](../../research/2026-11-17-rms-constants/README.md#the-coefficient-for-budgets-of-at-least-25).
They are now part of the library, where CI builds and audits them. This
record holds the audit runs made when they were added, at commit
[`7ed941f198939a95f282e491c66a2defeef0528b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/7ed941f198939a95f282e491c66a2defeef0528b).

## Statements

[`lean/ThresholdHC/LargeBudgetRMS/Specification.lean`](../../lean/ThresholdHC/LargeBudgetRMS/Specification.lean)
states four targets against the original experiment, risk and modulus
definitions, the same ones that the [sharp RMS constant](../sharp-rms-20261117/README.md)
uses. With $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `bracket_lower` | $R_\mu(B)\ge0.175198\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge25$, and the same for the revealed- and the selected-magnitude minimax risks. |
| `hundred_lower` | The same three bounds with $0.17807955$ for every $B\ge100$. |
| `fifth_gap_upper` | $R_{\delta_{1/5}}(25)\le0.186752$. |
| `bracket_upper` | If $R_\mu(B)\ge c\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge25$, then $c\le0.186752$. |

So the largest constant valid for every gap law at every budget of at least
25 lies in $[0.175198,0.186752]$. Its exact value is open. The
specification was written after the proofs; it is pinned by hash from this
audit onward.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_large_budget_rms.py --replay --jobs 3` | 25 exact statements and 147 transitive axiom reports over 28 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 28 modules replayed through the independent kernel checker. About 3 minutes on four cores with the modules already built; the first build of the modules took about 12 minutes. | [large-budget-rms-audit.log](large-budget-rms-audit.log) |
| `python tools/verify_project_axioms.py` | 15,560 constants (12,461 theorems) in 1,349 modules, same axioms. 141 exported instances. 2,965 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_large_budget_rms.py'` | 11 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,350 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
166 entries to `tools/definition_lock.json`: 115 public and 51 private
definitions of the new directory. No existing entry changed. The run
recorded here is the later one without that flag. Both runs were made with
the Lean sources of the commit above; the second was made one commit later,
which changes only the toolkit.

The 25 exact statements are the four targets, twenty component theorems
and the exact value of the pilot policy's worst squared risk. The
components include two intermediate results that the targets improve: the
coefficients $0.17356166$ for $B\ge25$ and $0.17623782$ for $B\ge100$ from
three sign biases, and the upper witness $0.195454$ from twenty-five fresh
flips. They are restated because the targets' proofs build on the same
modules.

## The certificates

The lower bound compares the fair-sign law with five pairs of sign biases.
Its pointwise inequality is checked by a degree-27 Taylor lower bound for
the exponential and exact polynomial comparisons on nine intervals. The
upper bound evaluates the worst squared risk of an 18-flip pilot followed by
seven adaptive choices: a polynomial in the fraction of positive signs,
compared with its endpoint value on eight rational subintervals. Lean
evaluates both by kernel reduction, with no native code; the kernel replay
re-evaluates them. The worst squared risk is exactly
$348763093753675683898541718818533\cdot10^{-34}$, attained when all signs
agree, and its square root is about $0.186751999656$.

## Provenance

[provenance.json](provenance.json) maps each of the 28 library modules to
the file of the research checkpoint `289438a` it comes from, with both
hashes. The 26 copied modules are identical to their research files up to
their import lines and line endings: the library uses LF, and 14 of the 26
research files use CRLF. They keep their research file names and their
namespaces (`ThresholdHC.SharpRMS.LargeBudget`, `.MultiBias`, `.Pilot`,
`.Revisit`). Their imports of research `Sharp*` files now point at the
`SharpRMS` modules that the [earlier record](../sharp-rms-20261117/README.md)
derived from the same checkpoint. Two modules are new: the specification
and `Full.lean`, which proves the four targets from the research theorems.

Five research files are not promoted: `RevisitCertificate`,
`RevisitExperiment`, `RevisitHistory`, `RevisitRisk` and `RevisitWitness`.
They prove the upper witness $0.188087$, which the pilot policy supersedes,
and no promoted module imports them.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. They do not show that a Lean type means what the paper says;
the [model-fidelity brief](../../docs/MODEL_FIDELITY.md) is the guide for
that comparison. The research package keeps its own replay records for its
files: [three biases](../../research/2026-11-17-rms-constants/large-budget-audit.json),
[five biases](../../research/2026-11-17-rms-constants/multi-bias-audit.json),
[pilot](../../research/2026-11-17-rms-constants/pilot-audit.json) and
[revisit](../../research/2026-11-17-rms-constants/revisit-audit.json).

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
