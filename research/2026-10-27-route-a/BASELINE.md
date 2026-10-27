# Baseline ledger — 27 October 2026

## Checkout and preservation

The supplied cwd is the parent of the repository. The actual checkout is
`C:/Users/User/Desktop/Projects/math/threshold-hillclimb`. Its configured
fetch/push origin is `https://github.com/davidiach/adaptive-threshold-estimation.git`.
The GitHub connector independently confirmed the public repository, ID
1434959790, default branch main, and matching clone URL. A shell `git ls-remote
origin HEAD` failed DNS; it did not change remotes. No push or remote-setting
change was performed.

Initial HEAD was 06af2df with seven modified paths: README.md, docs/RESULTS.md,
docs/VERIFY.md, paper/UPDATES.md, results/constants_last.json,
results/lean_score.json, results/uniform713_build.log. While this task was
reading, other activity committed 33eeeff and cleaned those changes; later
12e73e5 was observed. This task did not reset, revert, clean, or stage them.
The baseline replay copied **current tracked working-tree bytes**, not merely
HEAD, into `../route-a-baseline-snapshot`; per-file hashes, HEAD before/after,
and status are in baseline-snapshot.json. Research/formal source hashes will
identify new work independently of this concurrently moving HEAD.

No applicable AGENTS.md was found in the ancestor directories or repository.
The historical BRIEF.md is present. The current user's instructions supersede
its machine-only objective, reset-on-rejection rule, and permission to leave
proof stubs. Frozen files, manifests, and toolchain/library pins remain fixed.

## Claims, exact formal scope, and replay

| Result | Paper / mathematical scope | Lean scope and recorded evidence | Current replay / critical gap |
|---|---|---|---|
| Unrestricted minimax law | All laws, fresh iid coin creation, RMS lower omega/64 and one law-independent upper family | Components in Tier1/2; no full algorithm-level theorem | Numeric/guard/integrity replay passes. Full fresh-coin realization/reduction and universal upper admissibility remain paper dependencies. |
| Unbiased iff I finite; VW>=I^2/16 | Uniform over all measurable q; fixed-gap sharpness | Fixed-gap/components; converse not full algorithm-level Lean | No new assertion of full formalization. |
| Existing 713 construction | Uniform arbitrary magnitude/sign laws | `Uniform713.full_bound_713`, locked specification; 130/130 recorded roots, complete, standard axioms | Full historical audit reused. Separate EY²<=23I and ET<=31I bridge being added; product alone does not justify product of separate suprema. |
| Tier3 optimizer | Exact arbitrary-law Psi variational identity | `Tier3.arbitrary_law_optimizer` and cutoff; complete Tier3 11/11, 152/152 recorded declaration audit | Nine-file lock rechecked. Optimizer supplies no attaining algorithm. |
| Tier3 stopping/testing | Arbitrary random seed and unbounded finite-mean work | Fixed finite coin family; 11/11 recorded targets | Independent historical Linux replay of23988c7 exists. Fresh creation remains outside scope. |
| Tier4 full transcript KL | Infinite observation tape, not infinitely many distinct coins | Complete at initial HEAD: 6/6 targets,65/65 roots, exit0; fixed `Fin m` family | Ten-file lock rechecked. No exact-current-commit CI found at initial query; historical CI is not new-state verification. |
| Rare-event Psi lower | All-adaptive fresh coins; global rarity constraint | No Lean theorem for this statistical lower bound | Imported Lee–Valiant Cor19 + bounded-ratio finite-prefix decomposition re-audited by reviewer; paper-proof status. |
| Rare-event upper | Continuation proves power margins 0<alpha<2 | No algorithm-level rare upper | Arbitrary laws and alpha>=2 were open at this baseline. |
| Unknown rarity | Exact fully uniform rho-independent guarantee impossible already at fixed interior gap | Paper proof with agent review | Separate from knowing rho; do not retry the refuted guarantee. |

The current paper is paper/paper.tex, preserved equal to imported baseline
inputs/next-phase/baseline/Adaptive_Threshold_v4/source/paper.tex. The continuation
is inputs/next-phase/report/research_note.tex; prior audit and reviews are under
inputs/next-phase/PRIOR_ART_AUDIT.md, proposals/RESEARCH_REVIEW.md, and imported
review/. Current scope is docs/RESULTS.md, commands docs/VERIFY.md, report and
append-only run log docs/process/REPORT.md and RUNLOG.md. TIER4.md documents
the newer completed development; the older report still calls that work open
and needs a concise current addendum, not an alternative historical narrative.

Locks/registries: FROZEN.sha256, TIER3_FROZEN.sha256, TIER4_FROZEN.sha256,
inputs/next-phase/MANIFEST_SHA256.txt; tools/targets.json,
uniform713_targets.json, tier3_targets.json, tier4_targets.json; experiment
locks results/constants_candidate_lock.json and results/real_selection.json.
Toolchain is Lean4 v4.36.0-rc1; library revisions in lean/lake-manifest.json.

## Checks run without overwriting published records

Exact commands, exit codes, elapsed times, and individual output logs are in
baseline-checks.json and baseline-logs/. Input preservation, experiment locks,
original freeze, both numerical target suites, 26 validation tests, power
quadrature, bias counterexample, uniform arithmetic, and all three existing
constant evaluations passed (exit0). These reuse stored held-out data; there
was no fresh confirmation set or retuning. Tier3/Tier4 closure locks also passed.

`benchmark/verify_real.py` initially exited1 because the byte-only snapshot
omitted ignored `.runtime/python` and could not import numba. Replaying with
PYTHONPATH pointing at the original runtime exited0:71,049 finite-tape checks,
1,000 telescopes,10 calibration checks, seed2026102603. This is an environment
repair, not a benchmark-source change. Full baseline Lean rebuilds are not
repeated solely to inflate evidence; new formal dependencies receive fresh
exact-type and transitive-axiom checks. Current research acceptance must record
any unavailable independent replay separately.

### Evidence arriving during this session

Another concurrent commit, ddf9501, added docs/TIER4.md updates and
results/tier4_linux_checkpoint.json. Read-only GitHub API checks subsequently
confirmed successful runs40470998119 at exact commit12e73e5963bb313250b87aaed0fc700cb4ee9e00
and40471311295 at proof commit06af2dfce31e0f768fd47bf1b94dd233fe3a2559.
The recorded audits cover Tier4 6/6 and65/65, Tier3 11/11 and152/152,
713 130/130, scalar7/7, and original121/121. This updates the earlier
initial-query availability statement. It verifies those older exact states,
not this session's new rare-event proof or additive bridge. The newly arrived
files were not edited or staged as this task's work.
