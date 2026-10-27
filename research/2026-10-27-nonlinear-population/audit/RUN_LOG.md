# Audit run log

All work in this pass used repository
`C:/Users/User/Desktop/Projects/math/threshold-hillclimb`, HEAD
`d75c775633df545b892e69fc876930d6d2dcc329`, Python 3.12.2. Writes by this
agent were restricted to this audit directory. No commit, push, external
message, old lock change, or Lean replay was performed by this agent.

Read complete current additive construction, concurrent nonlinear-critical
review/source notes, upper bounded-depth and subsequent depth-tail proof,
lower feedback proof and certificate, local information note, and the
parent's full frozen experiment implementation and contract. Source hashes
are recorded in REVIEW.md and the JSON outputs. This is source inspection
at the indicated checkpoints, not a claim about uninspected later changes.

Fresh primary-source browsing inspected:

- Lee--Valiant v3, https://arxiv.org/html/1904.09228v3 and
  https://arxiv.org/pdf/1904.09228v3; Section 7's optimization construction,
  Lemmas 22--23, Theorems 4--5, and Appendix C's coefficient calculation.
- Juditsky--Nemirovski, https://www2.isye.gatech.edu/~nemirovs/AnnStat_Saddle_2009.pdf;
  Section 2.1, Theorems 3.1--3.2, Lemmas 3.1--3.2, Proposition 3.1.

These are the actual sources read; the focused comparison and unresolved
application issues appear in LV_AND_PILOT.md. No broad literature audit or
priority certification is asserted.

An initial importlib execution independently called the lower certificate's
`certify(*case)` for each of its three cases and wrote
`feedback_replay.json`, without invoking the certificate's main writer.
It records before/after source hashes. The later saved reproducible replay
below repeats all these cases.

Commands actually run from repository root:

```powershell
python research/2026-10-27-nonlinear-population/audit/replay.py
python research/2026-10-27-nonlinear-population/audit/check_experiment.py
python research/2026-10-27-nonlinear-population/audit/replay.py replay_final.json
python research/2026-10-27-nonlinear-population/audit/check_experiment.py experiment_audit_final.json
```

All returned exit code 0. The first replay preceded the depth-tail extension
and wrote `replay.json`: K=1..16 polynomial identities, 31 local words,
1,024 capped feedback transcripts, critical-law FI values, 48 rational
clipping examples. It used exact Fraction arithmetic and no random seed.

The experiment audit wrote `experiment_audit.json`. It checked original
source/contract/lock/raw hashes, repeated the finite predictive and variance
reduction identity checks, and read all 7,680 stored rows. It did not rerun
Monte Carlo or manufacture a new held-out sample.

The final replay wrote `replay_final.json`, adding 1,024 depth-tail
transcripts and the three exact lower feedback certificates. It records
matching before/after final source hashes. Finite calculations supplement
the all-K/all-policy paper proof; they do not formally establish it.

The current replay refuses to overwrite an existing output; on a clean
checkout choose a fresh name, for example:

```powershell
python research/2026-10-27-nonlinear-population/audit/replay.py replay_local_new.json
```

The experiment audit similarly refuses to overwrite its saved JSON. A final
execution added its own checker hash to `experiment_audit_final.json`, with
the same experiment inputs and assertions. Its read-only assertions can be
replayed to a fresh output without modifying any locked experiment inputs:

```powershell
python research/2026-10-27-nonlinear-population/audit/check_experiment.py experiment_local_new.json
```

One attempted prose-only patch to the clipping note failed its context match;
no file changed in that failed attempt. A subsequent exact-context patch
succeeded. The final proof body is the independently reviewed one, with
added review provenance and the base-risk qualification. No failed
mathematical or arithmetic check was concealed.
