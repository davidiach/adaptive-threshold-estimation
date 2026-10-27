# Lean environment and Phase 0 evidence

Track A ran on Windows with Lean `v4.36.0-rc1` (commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`) and Mathlib commit
`9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`. The exact dependency revisions are
in `lean/lake-manifest.json`; the original target statements elaborated
without edits. No Phase 0 statement repair was necessary.

Elan was installed inside the ignored `.runtime/elan` directory without a
system PATH change. To use that installation in a PowerShell session from
the repository root:

```powershell
$env:ELAN_HOME = Join-Path (Get-Location) '.runtime/elan'
$env:PATH = "$env:ELAN_HOME\bin;$env:PATH"
$env:PYTHONUTF8 = '1'
python tools/score.py
```

A normal externally installed `elan`/`lake` also works. For a fresh machine,
install the toolchain specified by `lean/lean-toolchain`, then run
`lake exe cache get` and `lake build` from `lean/`. Do not run `lake update`
on the frozen repository: the manifest is part of the integrity check.

The cache downloaded and decompressed all 9,076 requested modules. The first
parallel local build reported two transient `.olean.private` read failures;
the immediate retry built the remaining modules and root successfully.
The statements were already successfully elaborated during the first build.
Sequentially building each proof module before the root is a conservative
option on machines with less memory.

Phase 0 score: valid, 0/60 points, 0/33 proved. An independent invocation of
`lake env lean .audit/Audit.lean` returned exit code 0 and all 33 axiom reports.
Every target was still a `sorry` stub at that checkpoint. The frozen scorer
does not include the audit process exit code in its overall `valid` field,
so subsequent claims also require the independent audit to exit 0 and emit
all 33 reports. The scorer was unchanged at that historical checkpoint.

The approved Tier 2 integration now enforces audit exit status and all 46 reports
in scorer v2, while retaining the independent checkpoint guard. Its scorer and
checkpoint/713 readers explicitly decode Lean's UTF-8 output, so Windows cp1252
defaults no longer break Unicode diagnostics. `PYTHONUTF8=1` remains useful for
other Python tools. See the approval and verification record in [FREEZE_LOG.md](../FREEZE_LOG.md).

Evidence: `results/lean_phase0_build.log`, `results/lean_phase0_retry.log`,
`results/lean_baseline.json`, `results/lean_baseline_direct_audit.log`, and
`results/lean_baseline_direct_audit_exit.txt`.
