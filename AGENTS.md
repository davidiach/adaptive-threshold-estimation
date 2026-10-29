# Agent working guide

This repository contains mathematical research, Lean proofs, Python tools, and
preserved research evidence. Start with the user's current task and keep changes
within its scope. Use this guide for repository operations and
[CONTRIBUTING.md](CONTRIBUTING.md) for setup and editing guidance.

## Find the current source of truth

- [README.md](README.md): problem, main results, and reading paths.
- [docs/RESULTS.md](docs/RESULTS.md): current mathematical claims, assumptions,
  and verification boundaries. Read the relevant section before changing a claim.
- [lean/README.md](lean/README.md): concept-to-module map and formal audit commands.
  The linked Lean specifications give the exact formal statements.
- [docs/VERIFY.md](docs/VERIFY.md#choose-checks-by-task): checks by task,
  prerequisites, output locations, and detailed audit scope.
- [docs/WORKPLAN.md](docs/WORKPLAN.md#current-priorities): current priorities;
  its expandable ledger preserves earlier checkpoints.
- [results/README.md](results/README.md): published evidence and how to interpret it.

[BRIEF.md](BRIEF.md) is the preserved original overnight assignment. Its initial
setup, scoring loop, and rollback commands are historical context, not the
default workflow for new tasks. Do not restart Phase 0 or follow its blanket
revert instruction. The frozen-source and held-out-data constraints remain in force.

## Preserve sources and evidence

- Check `git status --short` before editing. Preserve unrelated and untracked
  work; isolate your changes when the checkout is shared or dirty. Do not use
  blanket restore, reset, or clean commands to discard a failed attempt.
- Treat files covered by `FROZEN.sha256`, `TIER*_FROZEN.sha256`, specification
  locks, and package manifests as immutable. Locks can cover proof dependencies
  and verification tools as well as statements. Never regenerate a lock, run
  `tools/freeze.py --init`, or run `lake update` to make a check pass. Changes to
  frozen material require explicit owner authorization and a recorded explanation.
- Preserve imported `inputs/`, sealed `research/` packages, published records in
  `results/`, and `paper/rare-event/v2/` and `paper/rare-event/audit/` byte for byte.
  Add corrections or new evidence separately with a clear source/checkpoint identity.
- Respect [.gitattributes](.gitattributes): manifests hash exact bytes. Avoid
  repository-wide formatting or line-ending conversion.
- Edit manuscript sources through the entry points in
  [CONTRIBUTING.md](CONTRIBUTING.md#where-to-edit). Do not hand-edit generated TeX
  or rebuild a published PDF in place during an unrelated task.
- Keep tuning separate from held-out evaluation. Replaying stored evidence does
  not authorize a new held-out selection experiment.

## Validate the change

Run commands from the repository root unless a guide says otherwise. Use the
[task table](docs/VERIFY.md#choose-checks-by-task) and relevant verifier regression
tests. Run the exact-type and transitive-axiom audit for affected Lean results;
compilation alone does not establish the published verification claim.

Some legacy verifiers overwrite tracked `results/` files. Run those in a disposable
checkout containing the change under review. Newer audits use `.runtime/` or
temporary directories; see the [tool index](tools/README.md). Do not replace
published evidence with a local rerun as a side effect of validation.

For navigation-only edits, check relative links and heading anchors, run
`git diff --check` and `python tools/freeze.py --verify`, and inspect the final
file list. A full Lean rebuild is unnecessary when proof sources, specifications,
tools, and dependencies are unchanged.

## Report accurately

Distinguish Lean-checked claims, paper proofs, finite or numerical evidence, and
conjectures. Keep assumptions and limitations attached to the claim. Historical
reports describe their own checkpoints and must not be silently upgraded.

Report changed files, checks actually run, and unresolved limitations. Identify
the commit for any CI claim; a saved successful audit or local pass is not evidence
that CI passed on a later commit. Update current navigation and claim summaries
when appropriate, while retaining the original historical records.
