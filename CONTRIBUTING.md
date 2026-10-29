# Contributing

Start with the [project overview](README.md) and the relevant section of the
[results guide](docs/RESULTS.md). This is a research repository: mathematical
claims, executable implementations, and archived evidence have different scopes.
AI agents should also read [AGENTS.md](AGENTS.md).

## Find your starting point

| Task | Start here |
|---|---|
| Read the mathematics | [Consolidated v5 paper](paper/v5/README.md), [general-law rare-event paper](paper/rare-event/README.md) and [finite-gap rare-event paper](paper/finite-gap-rare-events/README.md) |
| Work on a formal proof | [Lean module map](lean/README.md), then the relevant specification and audit |
| Use or change the Python estimators | [Toolkit guide](toolkit/README.md) and `toolkit/tests/` |
| Run or maintain verification | [Checks by task](docs/VERIFY.md#choose-checks-by-task) and [tool index](tools/README.md) |
| Interpret a stored result | [Evidence index](results/README.md) and [research package index](research/README.md) |
| Choose follow-up work | [Current priorities](docs/WORKPLAN.md#current-priorities) |

The root [BRIEF.md](BRIEF.md) preserves the original overnight assignment.
Its initial setup and hill-climbing instructions describe that run. Use this
guide for new contributions; retain the brief and its frozen-source and
held-out-data constraints. [Process history](docs/process/README.md) explains
why these records remain in their existing locations.

## Set up a working checkout

Check `git status --short` and work on a focused branch. Use a separate checkout
or worktree if another task has local changes. Preserve unrelated files and
undo only your own edits when an approach fails.

Research verification uses Python 3.12. A virtual environment is recommended;
activate it using your shell's normal command, then run from the repository root:

```sh
python -m pip install -r requirements.txt
```

For toolkit development, install the package and run its tests:

```sh
python -m pip install -e ./toolkit
python -m unittest discover -s toolkit/tests -v
```

The toolkit supports Python 3.10 or newer. Lean work additionally needs `elan`
and the [pinned toolchain and Mathlib cache](docs/VERIFY.md#setup).
The existing CI runs on Linux; the Python and Lake commands also apply to
Windows with those tools on `PATH`. Historical machine-specific paths are not
portable setup instructions. LaTeX tools are needed only for manuscript builds;
each manuscript README gives its build command.

## Where to edit

| Area | Editing guidance |
|---|---|
| `README.md`, `docs/`, and directory indexes | Maintain current explanations, navigation, and status. Preserve the historical records under `docs/process/`. |
| `lean/ThresholdHC/` | Use the [module map](lean/README.md). Inspect the applicable manifest or specification lock before editing: locks can include proof files and model dependencies. |
| `tools/` | Verifiers, regression tests, registries, and manuscript generators. Some tools are frozen; check the [tool index](tools/README.md) and the applicable locks. |
| `toolkit/` | Python package, examples, and tests. Its implementation is not itself Lean-verified. |
| `paper/v5/` | Edit `frontmatter.tex`, `constant713.tex`, `rare-events.tex`, `verification.tex`, and layout in `main.tex`. Use the [source and regeneration guide](paper/v5/README.md#source-and-editorial-scope). |
| `paper/critical-review/` | Edit the brief in `overview.tex`; regenerate `main.tex` with `tools/build_critical_review.py`. See the [packet guide](paper/critical-review/README.md). |
| Shared manuscript additions | Edit `paper/finite-gap-extension.tex` for the shared addendum, then regenerate the affected projects. Do not edit generated copies directly. |
| `inputs/`, sealed `research/` packages, rare-event `v2/` and `audit/`, and `paper/finite-gap-rare-events/` | Preserve the imported or published payloads; the finite-gap paper's `SHA256SUMS` lists its locked files. Put new work or explicit corrections alongside them rather than rewriting their evidence. |
| `results/` | Preserve published records. Fresh runs belong in temporary output or a disposable checkout; see [evidence handling](results/README.md#fresh-runs-and-publication). |
| `benchmark/` and `constants/` | Read the [benchmark protocol](benchmark/README.md) and applicable locks before changing experiments or scoring. Keep held-out data out of tuning. |

The v5 generator owns `introduction.tex`, `core.tex`, the three `appendix-*.tex`
files, `references.tex`, and the local `finite-gap-extension.tex`. Regenerate
these only when the task changes their inputs. A documentation cleanup does
not require rebuilding published manuscripts.

## Preserve reproducibility

Frozen sources and manifests are part of the research contract. This includes
`FROZEN.sha256`, the tier manifests, specification/dependency locks, and package
manifests. Obtain explicit owner authorization for changes to frozen material
and record the reason; never update a hash merely to silence a failed check.
Keep the pinned Lean/Mathlib dependencies and exact line endings intact.

Published audits describe a particular source state and scope. Add a new,
identified record when publishing new evidence; keep the prior record unchanged.
Use the [current results guide](docs/RESULTS.md) to explain later developments
instead of revising a historical report to claim it verified them.

## Check and submit

Choose checks from [VERIFY.md](docs/VERIFY.md#choose-checks-by-task). For a
documentation-only change, validate relative links and heading anchors, run
`git -c core.whitespace=cr-at-eol diff --check` and `python tools/freeze.py --verify`, and confirm that the
diff contains only intended documentation. The `cr-at-eol` setting keeps
CRLF files such as `docs/VERIFY.md` from being reported as trailing whitespace;
`freeze.py --verify` covers only `FROZEN.sha256`, so run the matching verifier
if the diff touches another locked path. Use the relevant proof, tool, toolkit,
or manuscript checks when those areas change.

Before submitting, inspect `git diff --stat` and `git status --short` for generated
logs, PDFs, or evidence rewritten by a local run. Keep the pull request focused;
describe the user-visible change, the checks actually run, and any limitations.
Claim CI success only for the commit whose jobs have completed successfully.
