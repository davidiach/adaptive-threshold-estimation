# Sharp RMS lower constant and square-root cap: library audit

The Lean proofs of the [RMS constants research package](../../research/2026-11-17-rms-constants/README.md)
are now part of the library, where CI builds and audits them. This record
holds the audit runs made when they were added, at commit
[`f1425008ea71094d900b8cbb9a90b485f0884d33`](https://github.com/davidiach/adaptive-threshold-estimation/commit/f1425008ea71094d900b8cbb9a90b485f0884d33).

## Statements

[`lean/ThresholdHC/SharpRMS/Specification.lean`](../../lean/ThresholdHC/SharpRMS/Specification.lean)
states eight targets against the original experiment, risk and modulus
definitions. With $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `sharp_lower` | $R_\mu(B)\ge\omega_\mu(B^{-1/2})/6$ for every gap law and every $B\ge1$. |
| `sharp_coefficient` | A constant $c$ satisfies $R_\mu(B)\ge c\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$ if and only if $c\le1/6$. |
| `sharp_endpoint` | $R_{\delta_{1/2}}(4)=1/6$. |
| `large_budget_lower` | $R_\mu(B)\ge\sqrt{59/2100}\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge25$. |
| `gap_reduction` | $R_\mu(B)\ge\omega_\mu(g)\,R_{\delta_g}(B)$ for every gap law, gap $g$ and budget. |
| `oracle_sharp_lower` | The bound of `sharp_lower` for the revealed- and the selected-magnitude minimax risks. |
| `oracle_large_budget_lower_bound` | The bound of `large_budget_lower` for both oracle risks. |
| `oracle_endpoint` | Both oracle risks equal $1/6$ at $\delta_{1/2}$ and $B=4$. |

[`lean/ThresholdHC/SquareRootCap/Specification.lean`](../../lean/ThresholdHC/SquareRootCap/Specification.lean)
states two targets for the optimized stopping programs, for rarity
$0<\rho\le1/2$:

| Target | Statement |
|---|---|
| `square_root_cap` | $P_N\le k\,G_N$ whenever $k>1$ and $B\le N(k-1/k)^2$. |
| `four_ninths` | If $N\ge4B/9$, then $P_N\le2G_N$ and $R\le P_N\le16R$. |

Both specifications were written after the proofs. They are pinned by hash
from these audits onward.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_sharp_rms.py --replay --jobs 3` | 38 exact statements and 343 transitive axiom reports over 54 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 54 modules replayed through the independent kernel checker. About 10 minutes on four cores with the modules already built. | [sharp-rms-audit.log](sharp-rms-audit.log) |
| `python tools/verify_square_root_cap.py` | 2 exact statements and 6 transitive axiom reports, same axioms. | [square-root-cap-audit.log](square-root-cap-audit.log) |
| `python tools/verify_project_axioms.py --replay-main-theorem --jobs 3` | 14,920 constants (11,988 theorems) in 1,321 modules, same axioms. 141 exported instances. 2,799 locked definition fingerprints. 204 main-theorem modules replayed. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_sharp_rms.py'`, and the same for `test_square_root_cap.py` | 16 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,322 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
178 entries to `tools/definition_lock.json`: 134 public and 42 private
definitions of `SharpRMS` and 2 of `SquareRootCap`. No existing entry
changed. The run recorded here is the later one without that flag.

The proofs keep 119 helper lemmas private. A private declaration has no
name an audit source can cite, so `verify_sharp_rms.py` does not list them
as roots. The whole-project audit checks their axioms with every other
constant, and the kernel replay covers them with their modules.

## The integer certificate

For intermediate budgets the proof compares 140 integer upper sums with
$2/3$, one for each bias interval of the window $[2/5,39/40]$. Lean
evaluates them by kernel reduction, with no native code: `checked_window`
depends on `propext` alone. In the research package the 140 comparisons
are one file, which takes about 22 minutes to compile and 20 more to
replay. In the library they are seven modules of twenty comparisons
(`WindowPart1` to `WindowPart7`), which Lake builds in parallel. The whole
`SharpRMS` target then builds in about 7 minutes on four cores, and the
replay of all 54 modules takes about 10.

## Provenance

[provenance.json](provenance.json) maps each of the 56 library modules to
the file of the research checkpoint `86bf31e` it comes from, with both
hashes. Of the 45 research files, 42 are identical in the library up to
their import lines and line endings; the library uses LF, where 48 of the
50 research Lean files mix CRLF and LF. The other three differ as follows:

- `SharpWindow.lean` is split as described above. The 140 comparisons keep
  their names, bounds and order, and become public theorems. Its
  `Decidable` instance is named `decidableGridBound`.
- In `SharpOracleLaw.lean` an anonymous instance is named
  `oracleArrayLaw_probability`.
- `SharpCap.lean` becomes `SquareRootCap/Full.lean`, with its namespace
  renamed, an import of the specification and the two target theorems.

Three modules are new: the two specifications and `SharpRMS/Full.lean`,
which proves the eight targets from the research theorems.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. They do not show that a Lean type means what the paper says;
the [model-fidelity brief](../../docs/MODEL_FIDELITY.md) is the guide for
that comparison. The sharp lower statement has the same form and uses the
same definitions as the frozen Tier 6 lower bound, with $6$ in place of
$64$.

The upper constant $512$ of the RMS law is unchanged. The other results of
the research package are paper proofs and are not part of this audit: the
factor $3\sqrt7/2$ between the infinite stopping program and minimax risk,
the sharp oracle upper constant $1/2$, and the oracle asymptotics.

The research package keeps its own replay records for its files:
[critical window](../../research/2026-11-17-rms-constants/sharp-critical-window-audit.json),
[ordinary model](../../research/2026-11-17-rms-constants/sharp-unrestricted-audit.json),
[oracles](../../research/2026-11-17-rms-constants/sharp-oracles-audit.json),
with a [second run on Linux](../../research/2026-11-17-rms-constants/sharp-oracles-linux-audit.json),
and [cap](../../research/2026-11-17-rms-constants/audit.json).

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
