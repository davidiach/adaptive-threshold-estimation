# Specialist review packet — unsent

Prepared 27 October 2026. **No correspondence has been sent. No human specialist review has been received.** Agent checks are internal evidence only. The current run's mathematical discoveries and exact remaining obligations should be read in `RESEARCH_NOTE.tex`, `CLAIMS.tsv`, and `FINAL_REPORT.md`; this packet focuses on the inherited critical lower bound and source positioning.

## Claim needing specialist assessment

Fix observed outer states U uniform on [0,1], binary inner observations X in {-1,1}, and a disclosed magnitude map D with uniform law on (0,1/4]. Let the conditional mean be an unknown sign times 2D. A fixed admissible class permits arbitrarily fine finite cell partitions with independent unknown signs per cell and a cellwise linear D map. No regularity connects signs in different cells. An algorithm may choose states arbitrarily, revisit them, draw iid outer states, and stop adaptively; charge every inner sample.

The v4 paper claims that uniform RMS error eps, or fixed-confidence absolute error eps, requires expected work of order `eps^-2 log²(1/eps)` and supplies a matching upper algorithm. The hard finite partition may depend on eps but belongs to one fixed union class. It is not a claim about one fixed finite partition.

Every hard model meets the specific GHA v2 assumptions with accuracy-independent constants: the normalized absolute conditional mean has density bounded by 2, and every standardized conditional kth absolute moment is at most `3^(k/2)`. An explicit verification and oracle comparison is in `LITERATURE_AUDIT.md` §1. Adding fixed per-outer-draw cost changes the stated upper bound by a constant; no free conversion to deterministic work is asserted.

## Exact evidence and limits

- Inherited source: `paper/paper.tex`, propositions `prop:outer` and `prop:continuous`, approximately lines 1154 and 1225. v4 was preserved.
- Lower proof: dyadic bands; many cells per band; balanced product sign priors; target concentration; history-uniform predictive KL; stopped-transcript testing.
- Scope: unrestricted adaptive observations within the class, including selected states; expected work; no cross-state regression assumptions; not a rare-positive subclass.
- Formal limit: ask `FORMAL_COVERAGE.md` for current rebuilt Lean coverage. A finite-coin information theorem does not by itself formalize this observed-state minimax construction or the iid countable-reservoir model.
- Priority: unresolved. The source audit is documented but neither exhaustive nor a priority certificate.

## Questions to ask a human reviewer

1. **Was this lower bound known?** Is there an earlier all-algorithm `eps^-2 log²(1/eps)` expected-work theorem for an observed-state conditional sampling oracle with only a bounded normalized-gap density and conditional moments? Please identify the precise theorem and oracle if so.
2. **Is the model comparison exact?** Are there any additional GHA assumptions or algorithmic conventions that exclude this fixed union class? Do arbitrary selected-state queries or disclosed magnitude maps create an overlooked information shortcut?
3. **Are the quantifiers correct?** Does the finite prior construction prove the stated uniform minimax lower bound on one fixed class, with constants independent of accuracy and cell count? Which measurability or unbounded-stopping steps need expansion?
4. **What scientific question does it settle?** Does this establish that the classical adaptive MLMC squared logarithm is unavoidable under the unstructured oracle, and only under that oracle? Is there a more useful framing that distinguishes smooth regression and known parametric simulators?
5. **Rare-event continuation:** Does the Lee–Valiant Corollary 19 import and bounded-relative-change hybrid decomposition correctly support the arbitrary-law lower functional Psi? Can a known adaptive linear-estimator theorem resolve the upper half without assuming knowledge of q-dependent sign-conditional magnitude laws?

## Comparisons reviewers should see

- [Lee–Valiant v3](https://arxiv.org/html/1904.09228v3): Lemmas 17–18, Corollary 19, Section 7. Strong existing adaptive decomposition and fixed-gap results; the finite-depth known-conditional-law optimization is a different input model.
- [Giles–Haji-Ali v2](https://arxiv.org/pdf/1802.05016v2): Assumptions 2.1, 2.4, Algorithm 1, Theorem 2.7. The intended exact comparison.
- [Broadie–Du–Moallemi author revision](https://moallemi.com/ciamac/papers/seqrisk-2010.pdf) and [Gordy–Juneja working paper](https://www.federalreserve.gov/pubs/feds/2008/200821/200821pap.pdf): different conditional Gaussian or joint-density premises; do not treat v4 as a lower bound for these full structured analyses.
- [Wang–Wang–Zhang v6](https://arxiv.org/html/2201.02958v6): cross-state RKHS smoothness changes the admissible class.
- [Chen–Naslidnyk–Briol v2](https://arxiv.org/html/2502.18284v2): smooth nested quadrature and function-evaluation access; its general lower-bound problem is not resolved by this construction.
- [Blum–Hu, Appendix G](https://home.ttic.edu/~avrim/Papers/TolerantTesting.pdf): explicit earlier adaptive good-arm fraction approximation, finite arms and a fixed gap. A newly located comparison in this audit, not a universal-law match.

## Draft correspondence — not sent

Subject: Request for a model and priority check of a nested-threshold lower bound

Dear colleague,

We would appreciate a specialist check of a claimed minimax lower bound for estimating `P(E[X|U]>0)` from charged conditional samples. The class has observed U uniform on [0,1], binary X, a uniform absolute-mean magnitude law, and no smoothness linking different states. The proposed lower rate is `eps^-2 log²(1/eps)` in expected work, even allowing selected-state queries. A finite-cell construction is embedded in one fixed admissible class and appears to satisfy Giles–Haji-Ali's normalized-gap density and conditional-moment assumptions with constants independent of accuracy.

We are not claiming novelty. We would like to know whether an equivalent lower theorem is already available, whether the oracle/assumption comparison is exact, and what conclusion is scientifically justified. The packet includes the unchanged v4 proof, a separate source audit, a claim ledger, and precise formalization limits. Any current rare-event results are explicitly separated from this inherited claim.

If you are willing to review a short extract, the main questions are the quantifier order, the adaptive selected-state information bound, and earlier results using the same observation model. No endorsement would be inferred from silence or an informal response.

With thanks,
Draft for the repository author to revise and send if desired

## Pending status

The new critical-margin result is also ready for separate mathematical review: under `F(x)<=(x/a)^2` and global rarity, the observable estimator in `theorem/critical.tex` has `EY²<=165rho/56` and `ET<=1350a^-2 L(1+log L)`. Please try to break the conditional-iid suffix argument, global-rarity rearrangement, separate moment/work bounds, or confidence amplification. The candidate lower scale omits `1+log L`; whether this factor can be removed or is necessary is open. The direct bounded-channel extension and observed shared-regression counterexample should be checked separately. These are paper proofs reviewed by agents only, not claims of external review or novelty.

Recipients have not been chosen or contacted. Send only after separate user authorization. This packet should be updated with the actual reviewer, exact reviewed version, date, and scope if a human assessment later arrives; until then all specialist judgments remain pending.
