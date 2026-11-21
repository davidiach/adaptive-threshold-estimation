# The explicit odd-Legendre pair of the bounded-depth obstruction: library audit

The bounded-depth obstruction of the nonlinear-population upper note
([`research/2026-10-27-nonlinear-population/upper/proof-body.tex`](../../research/2026-10-27-nonlinear-population/upper/proof-body.tex),
Lemma `lem:poly` and Theorem `thm:cap`) shows that a per-coin cap of $2K$
flips leaves the rare target unidentified on the exact quadratic law, even with
arbitrary cross-coin feedback. Its population half, the transcript identity and
floor for any pair of sign laws with matching odd moments, has been
Lean-checked since 21 November 2026
([record](../depth-obstruction-20261121/README.md)); the explicit pair was not.
The secondary-claims guide retained it as a paper proof
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md)). Lean now checks
it, in
[`lean/ThresholdHC/DepthLegendre`](../../lean/ThresholdHC/DepthLegendre/Full.lean).
The research package is unchanged. The audit runs below were made at commit
[`451ec2b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/451ec2b).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/DepthLegendre/Specification.lean)
defines the Legendre polynomial `legendre n` by Rodrigues' formula
$P_n=(2^nn!)^{-1}\,d^n/dx^n\,(x^2-1)^n$, as in the source (not Mathlib's shifted
Legendre polynomial); the slope $c=P_{2K+1}'(0)$; the polynomial
$u_K=c^{-1}\,\mathrm{divX}\,P_{2K+1}$; $m_K=1/((K+1)(2K+1))$; and the
allocations $q_\pm(d)=(1\pm u_K(d/h))/2\cdot\mathbf 1\{d\le h\}$ with
$h=a\sqrt\rho$.

| Target | Statement |
|---|---|
| `depth_polynomial` | `lem:poly`: for $K\ge1$, $c\ne0$, $u_K(x)=P_{2K+1}(x)/(cx)$ for $x\ne0$ and $u_K(0)=1$; $u_K$ is even of degree $2K$, $\lvert u_K\rvert\le1$ on $[0,1]$, $\int_0^1x^{2j+2}u_K=0$ for $j<K$, and $\int_0^1 2xu_K=m_K$. |
| `depth_pair` | For a probability gap law with the exact quadratic law on $(0,a]$, $0<a<1/2$, $0<\rho\le1/4$ and $K\ge1$: both allocations are sign laws and rare, with targets $\frac\rho2(1\pm m_K)$ and separation $\rho/((K+1)(2K+1))$; their odd gap moments agree through depth $2K$, and every coin word of length at most $2K$ has the same probability under both. The separation is at most the cap-$2K$ diameter of `CapIdentification` (a Lean-only conjunct). |
| `depth_cap_floor` | Under the same hypotheses, every procedure obeying the per-coin cap $2K$ has the same joint law of seed and observed transcript under the explicit pair, and RMS error at least $\rho/(2(K+1)(2K+1))$ over the pair and over the rare-prior risk. |

The equality of the whole seed-and-transcript law is stronger than the source's
equality of finite-prefix laws, and needs no almost-sure termination
hypothesis; neither statement has a work or budget hypothesis, as in the
source's "regardless of its expected total work". The hypotheses are the
source's; the proofs use only $a\le1/2$, $\rho\le1$ and $K\ge1$. The depth-tail
bound `thm:tail` ($p_K\ge1-4\varepsilon^2/\Delta_K^2$) is not part of this group.

## How the proofs go

- [`Rodrigues.lean`](../../lean/ThresholdHC/DepthLegendre/Rodrigues.lean): the
  Legendre equation through the Leibniz rule, the coefficients and their
  parity, $P_n(1)=1$, and $\lvert c\rvert\ge1$ from $4^K\le(K+1)\binom{2K+1}{K}$
  in place of the source's ratio argument.
- [`Polynomial.lean`](../../lean/ThresholdHC/DepthLegendre/Polynomial.lean) and
  [`Energy.lean`](../../lean/ThresholdHC/DepthLegendre/Energy.lean):
  $P_{2K+1}=cxu_K$, evenness and degree, the equation for $u_K$, and the
  source's energy argument for $\lvert u_K\rvert\le1$.
- [`Moments.lean`](../../lean/ThresholdHC/DepthLegendre/Moments.lean): the
  moments by a Green identity on $[0,1]$ from the Legendre equation, in place
  of the source's $n$-fold integration by parts on $[-1,1]$.
- [`QuadraticLaw.lean`](../../lean/ThresholdHC/DepthLegendre/QuadraticLaw.lean),
  [`Pair.lean`](../../lean/ThresholdHC/DepthLegendre/Pair.lean) and
  [`Floor.lean`](../../lean/ThresholdHC/DepthLegendre/Floor.lean): the change
  of variable $d=hx$ under the quadratic law, the pair's targets and matching
  odd moments, then `DepthObstruction.capped_transcript` and `equal_law_floor`.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_depth_legendre.py --replay --jobs 2` | 7 exact statements (the 3 targets and 4 components) and 72 transitive axiom reports over the 9 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 9 modules replayed through the independent kernel checker. | [depth-legendre-audit.log](depth-legendre-audit.log) |
| `python -m unittest discover -s tools -p 'test_depth_legendre.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 20,213 constants (16,320 theorems) in 1,685 modules, same axioms. 155 exported instances; 6 registered orphans, unchanged. 3,747 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,686 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 9
entries to `tools/definition_lock.json`: the three statements, the five
definitions above and the energy used in the sup bound. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which kept the
statements, checked the Rodrigues and energy steps by hand, and asked for the
change-of-variable lemma to carry its law hypotheses and be registered as a
component. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them:
- rebuilt the modules and printed the axioms of all public declarations;
- restated the targets and components with their types written out;
- instantiated the floor at $a=\rho=1/4$, $K=1$ with the never-querying estimator, giving a rare-prior risk at least $1/48$, and checked $c=-3/2$ and the $x^2$ coefficient $-5/3$ of $u_1$ against the paper.

It found no defect in the Lean. Its minor points concerned source line
numbers cited in docstrings, corrected before the pin, and the location of the
implementer's report. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
