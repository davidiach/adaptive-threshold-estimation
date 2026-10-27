# Nonlinear critical-regime research contract

27 October 2026. Starting checkpoint: d75c775633df545b892e69fc876930d6d2dcc329,
already pushed to origin/research/rare-minimax-20261027. The checkout remains
threshold-hillclimb and origin is davidiach/adaptive-threshold-estimation.
Uncommitted Tier5 and population-step work belongs to other activity and is
read-only for this task. All earlier locks and evidence are preserved.

## Principal target and experiment

Resolve the critical exact law F(d)=(4d)^2 on (0,1/4], with known mu,rho and
0<rho<=1/4, in the ordinary iid hidden-coin experiment. Every measurable
q:(0,1/4]->[0,1] satisfying integral q dmu<=rho is eligible. Policies see only
an independent seed and observed flips. They may create, revisit and interleave
coins, use unbounded stopping, depend on B,rho,mu, and return biased nonlinear
outputs. Uniform expected charged work is at most B>=1; loss is worst-case RMS.

Either prove R<=C Psi(B^-1/2) with a universal C, or refute it and give a sharp
replacement. The exact candidate is comparable to
min{rho,sqrt(rho L/B)}, L=1+log(1/rho). The inherited upper is
min{rho/2,C sqrt(rho L(1+log L)/B)}. The previous checkpoint proves the latter
order sharp only for its specified additive class.

## Triage and evolving dependency graph

First target: determine whether arbitrary nonlinear aggregation of independent
coin experiments escapes the additive obstruction. Juditsky--Nemirovski's
primary finite-discrete/Poisson convex-estimation framework is directly
relevant, but its confidence guarantee needs a proved RMS conversion.
Finite products, not arbitrary shared-seed mixtures, satisfy its hypotheses.
Fallback: a complete theorem for fixed independent designs and Poisson iid
replication, allowing arbitrary nonlinear terminal outputs. Such a theorem
would narrow the open problem but would not itself settle interactivity.

A stronger route emerged during the attempt. The inherited entropy argument
appears to charge only all-negative work W0, and survives restriction to
Xrho={q<=1/2, integral q<=rho}. This gives the proposed chain:

    small-bias V*W0 lower bound
    -> finite-experiment Hellinger hard pair for every capped policy
    -> one pair for every policy, by convex minimax and compactness
    -> finite-prefix all-adaptive Hellinger bound using midpoint simulations
    -> unbounded expected-budget RMS lower bound.

The midpoint satisfies q<=1/2, hence its work dominates W0/2. This alignment
is essential; a product involving only sup_q work cannot replace it. If every
step holds, the result is the sharp full critical rate with the extra factor
sqrt(1+log L), refuting the proposed Psi upper bound. Until the complete proof
passes review this is a proposed claim, not an accepted theorem.

## Decisive failure tests and evidence rules

Attack the minimax order, convexity/compactness, revealed versus hidden policy
mixing, endpoint and midpoint cost laws, seed access, finite-to-unbounded
passage, zero-work policies, saturation and small-rho joint limits. The
concurrent population-step radial result rules out assuming the natural radial
path is the needed hard pair; the proposed minimax pair may be nonradial.
No restricted numerical optimum is an all-policy converse.

The parent owns unrestricted.tex and integration. The construction agent owns
affine_comparison.tex and its fixed-design extensions. The foundations agent
owns base_cost.tex and supporting notes. The adversarial agent owns the full
review and source comparison, and does not author the proof it judges. Other
agents may review components they did not write; that does not create a second
independent review of their own work. Model diversity is not guaranteed.
New results are paper proofs unless separately specified and kernel checked.
No old frozen files are edited; no full-paper Lean completion is implied.

The user authorized pushing accepted work. Only task-owned reviewed changes
will be committed and pushed; unrelated working files and other branches are
preserved. External specialist contact is not authorized.

## Outcome

The complete full-model lower bound passed independent adversarial review,
with the existing matching upper. The exact critical-law rate has the extra
sqrt(1+log L) factor and refutes the proposed universal Psi upper. The final
scope, four-file reviewed identity, validation and limitations are in
CHECKPOINT.md; earlier provisional paragraphs record the research contract.
