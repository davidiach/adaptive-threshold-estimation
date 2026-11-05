# Require a successful audit process in a future scorer revision

**Status: source-inspection finding; not used to claim points.**

**Update: implemented in scorer v2 (Tier 2 integration, 27 October 2026; see
[FREEZE_LOG.md](../FREEZE_LOG.md)).** `tools/score.py` now sets `valid` only
when the audit process exits 0 and every target reports `proven` or `sorry`.
It records `audit_exit_code` and `audit_complete` rather than a separate
`audit_ok` field. The text below records the original finding against the v1
scorer.

`tools/score.py` records the return code from `lake env lean .audit/Audit.lean`,
but does not incorporate that code into `valid`. It also does not require that
all targets have an axiom report. Individual target-line errors are detected,
but a nonzero audit exit outside those lines can leave the overall validity
flag true and allow points from the reports that did appear.

This does not establish that any current proof is invalid. It is a reporting
gap: a successful build and some printed audit results do not themselves
establish that the complete audit command succeeded.

A future, separately approved scorer version should require audit return code
zero and complete target reports, explicitly record `audit_ok`, and retain the
present type/axiom checks. The scorer was unchanged when this note was written.
For this run, the audit process should also be replayed directly and checked
for a zero exit before publishing a successful proof checkpoint.
