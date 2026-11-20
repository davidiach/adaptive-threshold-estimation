# Paper corollaries: library audit

The guides stated three consequences of Lean-checked theorems as paper
arguments only. Lean now checks all three, in
[`lean/ThresholdHC/PaperCorollaries`](../../lean/ThresholdHC/PaperCorollaries/Full.lean).
The audit runs below were made at commit
[`82f0de32ac01336e14c610a0db17a334f6ef20b3`](https://github.com/davidiach/adaptive-threshold-estimation/commit/82f0de32ac01336e14c610a0db17a334f6ef20b3),
which adds the audit tool to the Lean commit
[`e5c53d53c13533a08b7335832786ff7e97953f7e`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e5c53d53c13533a08b7335832786ff7e97953f7e).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/PaperCorollaries/Specification.lean)
states three targets, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$.

| Target | Statement | Before |
|---|---|---|
| `envelope_rms` | Under a stochastic envelope, $\nu((0,t])\le\mu((0,t])$ for every $t$: for $B\ge1$ the minimax RMS risk over all gap laws $\nu$ below $\mu$ lies between $\tfrac16\,\omega_\mu(B^{-1/2})$ and $12\,\omega_\mu(B^{-1/2})$. | Lean had $1/64$ and $512$; the guide stated $1/6$ as a paper step. |
| `hard_sharp_lower` | With at most $\lfloor B\rfloor$ observations on every path, for $B\ge1$: $R^{\rm hard}_\mu(B)\ge\tfrac16\,\omega_\mu(B^{-1/2})$. | Lean had $1/64$; the guide stated $1/6$ as a paper step. |
| `psi_sequence` | At the quadratic law $F(d)=(4d)^2$, along $\rho_n=\exp(-e^n)$ and $B_n=\rho_n^{-2}$, for every $n\ge3$: $R_{\mu,\rho_n}(B_n)\ge7\cdot10^{-20}\sqrt{1+\log(1+\log(1/\rho_n))}\;\Psi_{\mu,\rho_n}(B_n^{-1/2})$, and the factor is at least $\sqrt{1+n}$. | The paper's sequence (v6 §14.4, Appendix F) was a paper derivation; the checked refutation of matching-$\Psi$ uses another budget. |

## How the proofs go

- **Envelope** ([`Transfer.lean`](../../lean/ThresholdHC/PaperCorollaries/Transfer.lean)).
  An algorithm admitted for the class of $\mu$ is admitted at $\mu$, so its
  risk is at least the sharp lower bound
  ([`sharp_lower`](../../lean/ThresholdHC/SharpRMS/Full.lean)). The
  distribution-blind family of the constant 12
  ([`blind_upper_12`](../../lean/ThresholdHC/UpperScale/Full.lean)) has risk at
  most $12\,\omega_\nu$ under every law $\nu$, and $\omega_\nu\le\omega_\mu$ below
  the envelope.
- **Hard cap.** A pathwise cap of $\lfloor B\rfloor$ observations meets the
  expected budget $B$, so $R\le R^{\rm hard}$.
- **The sequence** ([`PsiSequence.lean`](../../lean/ThresholdHC/PaperCorollaries/PsiSequence.lean)).
  With $\ell=e^n\ge e^3\ge20$, $\rho=e^{-\ell}$ and $B=\rho^{-2}$, the window rate
  of the [critical window](../critical-window-20261120/README.md) is
  $Y=4\rho\sqrt{\rho\ell(1+\log N_2)}\le\rho$, because
  $16\ell(1+\ell)\le\ell^5/120\le e^\ell$. The ratio statement of Corollary
  14.14 then gives $R\ge10^{-19}\sqrt{1+\log N_2}\,\Psi$. Since
  $N_2^2\ge1+\ell$, $1+\log N_2\ge\tfrac12(1+\log(1+\ell))$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_paper_corollaries.py --replay --jobs 3` | 5 exact statements (3 targets and 2 components) and 11 transitive axiom reports over the 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [paper-corollaries-audit.log](paper-corollaries-audit.log) |
| `python tools/verify_project_axioms.py` | 16,479 constants (13,307 theorems) in 1,425 modules, same axioms; 3,036 locked definition fingerprints. | [project-audit.log](../critical-window-20261120/project-audit.log) of the critical-window record, the same run |
| `python -m unittest discover -s tools -p 'test_paper_corollaries.py'` | 11 guard tests pass. | |

The three statement definitions were added to `tools/definition_lock.json`
with `--add-definitions`; no existing entry changed.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. `psi_sequence` concerns the rare-event experiment
of `RareAboveTwo` for an exact power law with $\alpha=2$, $a=1/4$. The checked
refutation of the matching-$\Psi$ conjecture in
[`CriticalPsi`](../../lean/ThresholdHC/CriticalPsi/Full.lean) is unchanged. The
hard-cap and envelope upper constants of other derived families (for example
$3000$ for the hard cap) are unchanged.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
