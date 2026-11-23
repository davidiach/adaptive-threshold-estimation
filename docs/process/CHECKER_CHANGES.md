# Checker changes

This log records every change to the checks' own trust anchors: a pinned
digest, a restated statement or target mapping, an entry of a lock or
manifest, the code of a checker, or a CI line that runs a check. The
[trust-anchor guard](../../tools/check_trust_anchors.py) lists such changes
on every pull request and every push to `main`, and fails until each one is
acknowledged here by a line that the same change adds. CI runs the copy of the
guard held by the base branch, so a change cannot edit the guard that judges
it.

Only changes and removals need an entry. Adding an audit, a pin, a restated
statement, a lock entry or a CI step adds checks and needs none. An entry does
not authorize a change to frozen material: that still needs the owner's
approval and a [FREEZE_LOG.md](../../FREEZE_LOG.md) record.

## How to add an entry

Run the guard against the branch the change will merge into:

```bash
python tools/check_trust_anchors.py --base origin/main --head HEAD
```

It prints one key per changed anchor. Add a section at the end of this file,
with a reason on a line that starts with `- Why:`, and the keys:

```markdown
## 2026-11-23 — Reject decide +native in the proof-escape scan

- Why: adds one alternative to the pattern and removes none, so the scan
  rejects more and accepts nothing new.
- Changes:
  - `code tools/verify_blind_upper_components.py _PATTERN@0123456789ab`
```

Say why the check had to change and why it is not weaker, or who authorized
a weaker one. A key names the old content, so an entry covers only the change
it was written for. Do not edit or delete earlier entries; the guard flags a
removed line.

## Entries
