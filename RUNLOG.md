# Run log (append-only)

One line per attempt, accepted or rejected:

`<UTC time> | track | change attempted | score before -> after | ACCEPT/REJECT | commit hash or note`
2026-10-26T21:46:05.3697509Z | B | 169 development-only parameter trials; lock theory-compatible then finite-grid candidates before held-out testing | dev 6.7788 -> 5.5506 / 4.2817 | LOCKED, not acceptance | see results/constants_candidate_lock.json
2026-10-26T21:47:01.8424405Z | B | prelocked k1=.25 k2=1 | dev 6.778762 -> 5.550646, heldout 6.771882 -> 5.550065 | ACCEPT | unchanged frozen scorer; see constants_theory_accept.log
2026-10-26T21:48:26.0039380Z | B | prelocked finite-grid k1=.25 k2=.5 | dev 5.550646 -> 4.281742, heldout 5.550065 -> 4.282066 | ACCEPT on frozen finite grid ONLY | uniform bias bound disproved; see proposals/constants/BIAS_AUDIT.md

Correction to Track B checkpoint digits: authoritative scorer JSONs give theory heldout=5.550060072084839 and finite-grid heldout=4.282068997489188. Earlier log entries transcribed intermediate messages inaccurately beyond four decimals; acceptance decisions and rounded summaries are unchanged.
2026-10-26T21:52:13.1883648Z | C | 342 tuning cells; selected randomized-sum method | tuning RMSE .02538/.01661 at 16384/65536 | LOCKED before heldout | results/real_selection.json, 500 planned final repetitions
2026-10-26T21:52:35.3521282Z | B/D | paper uniform product bound 713 and unknown-rarity obstruction independently reviewed | 12665 -> 713 for k1=.25,k2=1 | PAPER PROOF, not Lean | exact arithmetic checks pass; proposals/RESEARCH_REVIEW.md
2026-10-26T21:55:24.7289256Z | C | locked candidate once-only heldout500 | RMSE .039103/.021845 vs GHA .029904/.020124 | REJECT | preserve failed experiment; no posttest tuning, see TRACK_C.md
2026-10-26T21:55:44.1881642Z | A | compile unchanged statements, freeze12files, baseline scorer and independent audit | 0/60, 0/33 proved | VALID BASELINE | independent audit exit0, all33 reports contain sorryAx; no target edits
2026-10-26T22:03:39.5753647Z | A | checkpoint001, elementary groups plus B1 and C1-C3 | 0 -> 34/60,23/33 targets | ACCEPT | full build/freeze/types/axioms; independent audit exit0,complete33
2026-10-26T22:10:42.8782876Z | A | checkpoint002, all remaining KL/Hellinger/modulus/dyadic targets | 34 -> 60/60,33/33 targets | ACCEPT | all12frozenfiles unchanged; audit exit0; standard3axioms only; no sorry
2026-10-26T22:10:42.8782876Z | repository | future Git commits attributed to David Iach via verified GitHub noreply | GitHub author=davidiach verified | APPLIED | earlier commit history retained per user request
2026-10-26T22:32:52.2747886Z | A-extension | full713 checkpoint001: concentration, stopping/coupling, geometric series, estimator, integration, fixed full theorem specification | 86/86 new roots; original33/33 and60/60 retained | ACCEPT COMPONENT CHECKPOINT, full713 still in progress | standard axioms only; results/uniform713_status.json
2026-10-26T22:38:21.1468982Z | A-extension | full713 checkpoint002: complete actual classifier, conditional estimator, arbitrary-law integration, unbiasedness, strict713 theorem | 130/130 roots; full_theorem_complete=true | ACCEPT FULL THEOREM | exact specification hash unchanged; only standard3axioms; originalfrozen12 unchanged
2026-10-26T22:45:43.5724174Z | A-extension verification | independent Linux replay of full713 proof852690a | 130/130 newroots and33/33 originaltargets,60/60; bothCIjobs succeeded | VERIFIED | https://github.com/davidiach/threshold-hillclimb/actions/runs/40414013439
2026-10-26T22:56:23.899599Z | A Tier 2 integration | approved Opus targets, scorer/coverage fixes, 713 transitive-definition lock, freeze21 | 60/60 -> 60/121; Tier 1 60/60, Tier 2 0/61 | APPROVED BASELINE EXTENSION, not a proof improvement | ten regressions; numeric33+13; independent audit46; full713 audit130; scalar7; all local CI gates passed
