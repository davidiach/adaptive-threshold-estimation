# Freeze log

Record every change made to a frozen file BEFORE `tools/freeze.py --init`
(Phase 0 compile fixes only). After freezing, changes need David's approval
and go here too, with the approval noted.

Format, one entry per change:

## <file> — <short title>
- Before: `...`
- After: `...`
- Why: elaboration error message, and why the meaning is unchanged.
