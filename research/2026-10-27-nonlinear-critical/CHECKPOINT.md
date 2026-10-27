# Full critical-law minimax checkpoint

**Status: paper proof with independent adversarial agent review and scoped
component cross-checks.** This is not a Lean-checked theorem, external specialist
review, or certification of novelty. The full proof is [unrestricted.tex](unrestricted.tex),
with three local inputs; [review.md](review.md) records acceptance of all four
exact source hashes. [second-review.md](second-review.md) states which components
its author could independently check. Model diversity is not guaranteed.

## Strongest statement and change from the starting point

Fix mu(dd)=32d dd on (0,1/4]. There are universal constants 0<c<C<infinity
such that, for every 0<rho<=1/4 and B>=1,

$$c\min\{\rho,\sqrt{\rho L H/B}\}\le R_{\mu,\rho}(B)
\le C\min\{\rho,\sqrt{\rho L H/B}\},\qquad
L=1+\log(1/\rho),\quad H=1+\log L.$$

Here R is the minimax RMS error over all measurable q:(0,1/4]->[0,1]
with integral q dmu<=rho. Algorithms may know mu,rho,B but not q; their
only data are their independent seed and observed Bernoulli flips. They
may create, revisit and interleave iid coins, use biased nonlinear output,
and stop at unbounded times. The budget is sup_q E_qT<=B. No magnitude or
sign oracle, known conditional sign laws, equality theta=rho, or globally
finite coin inventory is assumed.

At the starting commit the matching lower bound covered only a specified
noninteractive additive class. The new lower bound covers the full experiment.
The upper was already present at a8a8dc4; it is reproduced with attribution,
not claimed as new. The variational identity is unchanged and gives
Psi(B^-1/2) comparable to min{rho,sqrt(rho L/B)}. Along
rho_n=exp(-exp(n)), B_n=rho_n^-2, both radii are unsaturated and R/Psi grows
at least as a positive constant times sqrt(H_n). Thus the proposed universal
matching-Psi upper bound is **refuted**, even for this one known law and known
rarity. The counterexample specifies the law and parameter sequence; the
least favorable population pair exists by compactness, without a closed formula.

## Proof dependencies and observation audit

| Paper target | Exact content | Evidence |
|---|---|---|
| `thm:base-cost` | For Xrho={q<=1/2, integral q<=rho}, bias<=rho/64 and finite separate uniform bounds imply V E_0T>=c rho L H. | Complete proof in base_cost.tex, including finite-gap Bernoulli sign entropy; independently reviewed. |
| `lem:comparison` | Finite positive affine categorical experiments admit an additive estimator with RMS <=12 times unrestricted RMS plus arbitrary slack; Poisson version also proved. | Full saddle and tail integration proof; established general principle credited to prior work. |
| `lem:hard-pair`, `lem:universal-pair` | One pair in Xrho, with prescribed separation, obeys H^2<=C delta^2 E_0T/(rho L H) for every capped one-coin policy. | Exact stopped-statistic reduction, finite revealed mixtures, convex minimax and weak-star compactness. |
| `lem:population-prefix` | The common pair gives H^2<=2 lambda E_mid T for every capped population algorithm. | Observable leaf factorization, normalized one-coin hybrids, data processing and midpoint domination of half the null law. |
| `thm:critical-minimax` | Full lower and existing matching upper, including saturation. | Same pair for all caps; endpoint almost-sure termination; terminal testing; separately finite upper moments and Poisson expected-budget replication. |

All conditional means are used only after finite moments are established.
Zero-observation procedures are handled before division. Positive finite
word probabilities follow from D<=1/4. Weak-star compactness uses equivalence
classes modulo mu-null sets and a closed global rarity constraint. Revealed
policy mixtures have an exact Hellinger average; no corresponding claim for
unrevealed mixtures is made. The simulated midpoint tapes are independent
proof seeds, not latent information given to the real algorithm. The cap
q<=1/2 is a lower-bound subclass, not a restriction on the upper theorem.
The unbounded limit uses finite work under both endpoints; it does not
transfer termination from just one population or differentiate an infinite law.

The upper includes an unbounded random level with finite mean work; a
Poisson number of genuine coins also has unbounded support. Its conditional
classifier/telescope proof and separate moment bounds are given in the
appendix. Constant output rho/2 supplies the zero-work saturation case.

## Starting ledger and preservation

The actual checkout is `threshold-hillclimb`, branch
`research/rare-minimax-20261027`, at starting commit
`d75c775633df545b892e69fc876930d6d2dcc329`. Origin is
`https://github.com/davidiach/adaptive-threshold-estimation.git`.
The user subsequently authorized pushing accepted work. No remote settings
are changed. [BASELINE.json](BASELINE.json) records current bytes, including
selected uncommitted neighboring sources; it is not a HEAD-only reconstruction.

| Starting material | What it established | What it did not establish |
|---|---|---|
| Preserved v4 paper and continuation | Algorithm-level ordinary minimax/unbiased paper arguments; rare variational optimizer and conjectured upper. | Full algorithm-level Lean proof; attaining arbitrary-law rare algorithm. |
| Uniform713 and separate RouteA bridge | Exact conditional-kernel Lean statements; separate EY²<=23I, ET<=31I and suprema product<=713I². | Fresh-coin realization or the new critical minimax theorem. |
| Tier3/Tier4 locks | Arbitrary-law variational optimizer; finite-family randomized/stopped/full-tape information statements. | A growing iid reservoir in the new rare-event lower bound. |
| Tier5 and neighboring population work | Separately owned ongoing creation/stopping work and radial diagnostics; only inspected for overlap. | Adopted dependencies or proof certificates for this theorem. |
| d75c775 paper checkpoint | Sharp additive-class critical rate, reviewed paper proof; local validation. | Nonlinear and interactive converse at that time. |
| a8a8dc4 critical upper | Observable critical upper with EY²<=165rho/56 and ET<=1350a^-2 L H. | Matching unrestricted converse at that time. |

No existing frozen source, manifest, tool, target registry, dependency pin,
imported manuscript, or published verification record is edited. Concurrent
Tier5, population-step, nonlinear-population and rare-event-probe files are
excluded from this checkpoint. Historical successful Lean evidence is reused
only for unchanged source identities; it is not evidence for the new theorem.

## Exact source identity and validation

The post-proof [paper lock](CHECKPOINT_LOCK_v1.json) covers the main source
and every local TeX input. It is an identity lock after paper review, not a
pre-proof Lean specification lock. No new Lean target is declared or accepted.

| Source | SHA256 |
|---|---|
| unrestricted.tex | b00b608ca1012148934e5717d2b10ee1d1379fa312a9f5bf06a0ac1e0e6fb853 |
| base_cost.tex | 6c02a467ac9a8b989ccb3e3618a9bb567e332ed1d3830d70fca27c01e5e3265a |
| affine_comparison.tex | c243a6ad355aeabb2fea3df195166faf066b95b4e5778e3bc02512d61a80f7c2 |
| upper_bound.tex | e4d8fd72f87fe0bf590b1cbbf8a61d9736f1402ba5e6a364df834cc810737fbc |

Run from the repository root:

```sh
python research/2026-10-27-nonlinear-critical/validate.py
```

The command creates a fresh timestamped `replays/` directory. An optional
`--output-dir` must name a nonexistent directory; it cannot silently replace
an old record. The accepted [validation.json](validation.json) records exact
commands, exit codes, starting commit, source snapshot, preserved paths,
locks and pending scope. The existing freeze/input guards and all current
validation regressions are included. Unchanged broad Lean builds and old
numerical searches are not repeated.

The acceptance replay exited 0: 490 protected starting paths and 78 prior
lock entries were unchanged, all 34 current guard regressions passed, and
all 17 scalar plus 22 finite-experiment checks passed. The paper lock SHA256
is `1e85c9e7a290e2b2cffde205934a08a289b48101fa30209e3a8a643cceb92131`.

`check_prefix.py` enumerates 20 finite atomic population experiments and two
stopped-statistic sufficiency cases. It uses exact rational probabilities
and work, and certified 160-bit dyadic square-root enclosures. Policies
include adaptive creation, revisiting, interleaving, early stopping and
revealed randomization, at caps 0,2,4,6; the largest tree has 185 seed/leaf
atoms. There is no Monte Carlo seed, optimization, grid-based lower-bound
claim, or held-out selection. The finite examples check decomposition,
normalization, cost charging and sufficiency; they do not prove the
continuum entropy bound or the common-pair theorem. Seventeen scalar
arithmetic checks likewise remain diagnostics. The first diagnostic's
rational-root enclosure issue and repair are disclosed in the second review.

The final four-file source compiled successfully with the desktop TeX compiler;
[compilation.json](compilation.json) binds that result to the bundle. Compilation
is typesetting evidence. Existing GitHub CI checks older formal/numerical
components, not this new mathematical proof; only a run on the exact pushed
commit can be described as regression evidence for that commit. No external
machine replay of the new research diagnostic is claimed here.

## Source comparison, strongest failed route, and limits

[sources.md](sources.md) records the actual Juditsky–Nemirovski,
Polyanskiy–Wu and Lee–Valiant statements/proofs inspected, including observation
models and unavailable Donoho–Liu body text. The earlier
[Route A source audit](../2026-10-27-route-a/sources.md) and
[critical audit](../2026-10-27-critical-two/sources.md) retain the Giles–Haji-Ali
nested-simulation comparison and Chen–Li–Qiao sign-entropy inspection.
Those are prior-art records, not external peer reviews. The new proof reproduces
its Bernoulli entropy and adaptive Hellinger inputs rather than silently
importing a Gaussian sign lemma or a fixed-conditional-law mixture bound.

The parent additionally inspected Sion's *On general minimax theorems*,
[publisher PDF, p.174](https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-p.pdf): the
convex compact theorem and its one-compact-domain corollary, including the
finite-cover reduction proof. Continuity and convexity/concavity in the two
uses are established in the note. Project Euclid's copy was blocked by its
access interstitial; the publisher PDF was accessible. No absence-of-predecessor
search certifies priority.

The strongest failed direct route tried to replace arbitrary terminal outputs
by additive estimators under shared random experimental design. That design
can destroy the required log-moment concavity. The independent-product and
Poisson comparison survives, but alone does not solve interaction. The
successful route instead extracts a common hard pair from all-negative cost,
then uses midpoint simulations. The neighboring radial-information proposal
was already refuted; the present theorem does not claim that radial profile
as its hard pair. [attempts.md](attempts.md) preserves these transitions, and
the companion construction.tex records the intermediate result.

The scientific change is a sharp full critical-law characterization and a
correction of the proposed statistical modulus. The convex-duality and
Hellinger tools are established prior work. Novelty of this application has
not been certified. The hard pair and constants are existential, and the
proof has no Lean verification. The next precise research question is a
sharp replacement for Psi on general magnitude laws, which must account for
the sign-testing cost across separated gap scales as well as rarity. The
current theorem answers that question only for the specified quadratic law.

The useful strategic change was aligning the cost law before doing the
minimax interchange. Further numerical tuning or more formal proof lines
would not have closed that statistical gap. Process history is retained in
the single current report and run log; imported baseline papers remain intact.
