# Run log (append-only)

One line per attempt, accepted or rejected:

`<UTC time> | track | change attempted | score before -> after | ACCEPT/REJECT | commit hash or note`
2026-10-26T21:46:05.3697509Z | B | 169 development-only parameter trials; lock theory-compatible then finite-grid candidates before held-out testing | dev 6.7788 -> 5.5506 / 4.2817 | LOCKED, not acceptance | see results/constants_candidate_lock.json
2026-10-26T21:47:01.8424405Z | B | prelocked k1=.25 k2=1 | dev 6.778762 -> 5.550646, heldout 6.771882 -> 5.550065 | ACCEPT | unchanged frozen scorer; see constants_theory_accept.log
