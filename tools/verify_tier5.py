"""Audit the separately locked Tier 5 extension without changing the 121-point scorer.

Every published Tier 5 declaration is kernel-audited. Available final theorems
also elaborate against their fixed statement types. Missing targets are pending,
never counted as proved; --require-complete rejects any such checkpoint.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
SOURCE = LEAN / "ThresholdHC/Tier5"
MANIFEST = "tools/tier5_targets.json"
LOCK = "TIER5_FROZEN.sha256"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(sorry|sorryAx|axiom|native_decide|implemented_by|extern|unsafe|opaque|run_cmd|run_elab|run_meta)\b"
    r"|skipKernelTC|#exit|#eval|\brun_tac\b|\bdebug\.|set_option\s+trust\b"
    r"|^\s*(?:(?:local|scoped)\s+)?(?:elab|macro|macro_rules|syntax|initialize|builtin_initialize)\b"
    r"|@\[\s*(?:command_elab|term_elab|tactic)\b", re.M)
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
    r"(?:def|abbrev|theorem|lemma|instance)\s+([A-Za-z_][\w']*)", re.M)
REPORT = re.compile(
    r"'([^']+)'\s+(depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.S)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments, preserving line breaks."""
    out: list[str] = []
    i = depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            out.append(" " * (end - i))
            i = end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)


def local_import_closure(module: str, root: Path) -> set[str]:
    seen: set[str] = set()
    pending = [module]
    while pending:
        current = pending.pop()
        rel = "lean/" + current.replace(".", "/") + ".lean"
        if rel in seen:
            continue
        path = root / rel
        if not path.is_file():
            raise ValueError(f"Missing specification dependency: {rel}")
        seen.add(rel)
        source = strip_comments(path.read_text(encoding="utf-8"))
        pending.extend(re.findall(r"^\s*import\s+(ThresholdHC[\w.]*)", source, re.M))
    return seen


def read_locks(root: Path = ROOT) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in (root / LOCK).read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        digest, rel = line.split(maxsplit=1)
        if rel in result or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError(f"Malformed or duplicate Tier 5 lock: {rel}")
        resolved = (root / rel).resolve()
        if not resolved.is_relative_to(root.resolve()):
            raise ValueError("Tier 5 lock escapes the repository")
        result[rel] = digest
    return result


def check_locks(manifest: dict, root: Path = ROOT) -> dict[str, str]:
    locked = read_locks(root)
    expected = local_import_closure(manifest["specification_module"], root)
    expected |= {MANIFEST, "tools/verify_tier5.py", "FROZEN.sha256", "TIER3_FROZEN.sha256", "TIER4_FROZEN.sha256"}
    if set(locked) != expected:
        raise ValueError("Tier 5 lock must cover the exact specification import closure and audit tools")
    for rel, digest in locked.items():
        if not (root / rel).is_file() or sha(root / rel) != digest:
            raise ValueError(f"Tier 5 specification/tool hash mismatch: {rel}")
    # Preserve every prior specification, checker, and lock manifest.
    for previous in ("FROZEN.sha256", "TIER3_FROZEN.sha256", "TIER4_FROZEN.sha256"):
        for line in (root / previous).read_text(encoding="utf-8").splitlines():
            if line.strip() and not line.startswith("#"):
                digest, rel = line.split(maxsplit=1)
                if not (root / rel).is_file() or sha(root / rel) != digest:
                    raise ValueError(f"Prior frozen hash mismatch in {previous}: {rel}")
    return locked


def declarations(path: Path) -> list[str]:
    source = strip_comments(path.read_text(encoding="utf-8"))
    if FORBIDDEN.search(source):
        raise ValueError(f"Forbidden proof escape: {path.name}")
    namespaces = re.findall(r"^\s*namespace\s+([\w.]+)", source, re.M)
    names = DECLARATION.findall(source)
    if names and namespaces != ["ThresholdHC.Tier5"]:
        raise ValueError(f"Audit registration requires the single Tier 5 namespace: {path.name}")
    return ["ThresholdHC.Tier5." + name for name in names]


def parse_reports(output: str) -> dict[str, list[str]]:
    reports: dict[str, list[str]] = {}
    for match in REPORT.finditer(output):
        name = match[1]
        if name in reports:
            raise ValueError(f"Duplicate axiom report: {name}")
        reports[name] = [] if match[3] is None else [a.strip() for a in match[3].split(",") if a.strip()]
    return reports


def valid_audit(returncode: int, reports: dict, expected: set[str], unchanged: bool) -> bool:
    return (returncode == 0 and set(reports) == expected and unchanged
            and all(set(axioms) <= ALLOWED for axioms in reports.values()))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--sequential", action="store_true")
    args = parser.parse_args()
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    status_path = results / "tier5_status.json"
    status_path.write_text(json.dumps({"valid": False, "complete": False,
        "error": "Verification has not completed successfully."}, indent=2) + "\n")
    manifest = json.loads((ROOT / MANIFEST).read_text())
    locked = check_locks(manifest)
    paths = sorted(SOURCE.glob("*.lean"))
    modules = [".".join(p.relative_to(LEAN).with_suffix("").parts) for p in paths]
    roots = [name for path in paths for name in declarations(path)]
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate Tier 5 declaration names")
    hashes = {str(p.relative_to(ROOT)).replace("\\", "/"): sha(p) for p in paths}
    targets = manifest["targets"]
    if len({t["theorem"] for t in targets}) != len(targets):
        raise ValueError("Duplicate Tier 5 targets")
    available = [t for t in targets if t["theorem"] in roots]
    pending = [t["theorem"] for t in targets if t["theorem"] not in roots]
    commands = [["lake", "build", m] for m in modules] if args.sequential else [["lake", "build", *modules]]
    logs = []
    for command in commands:
        build = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        logs.append(build.stdout + build.stderr)
        if build.returncode:
            (results / "tier5_build.log").write_text("\n".join(logs), encoding="utf-8")
            raise ValueError(f"Tier 5 build failed: {command}")
    (results / "tier5_build.log").write_text("\n".join(logs), encoding="utf-8")
    lines = ["import " + module for module in modules]
    lines += ["namespace ThresholdHCTier5Audit"]
    exact_roots = []
    for target in available:
        name = "audit_" + target["theorem"].rsplit(".", 1)[-1]
        lines.append(f"theorem {name} : {target['statement']} := {target['theorem']}")
        exact_roots.append("ThresholdHCTier5Audit." + name)
    lines += ["end ThresholdHCTier5Audit"]
    expected = set(roots + exact_roots)
    lines += ["#print axioms " + name for name in sorted(expected)]
    audit = LEAN / ".audit/Tier5.lean"
    audit.parent.mkdir(exist_ok=True)
    audit.write_text("\n".join(lines) + "\n", encoding="utf-8")
    run = subprocess.run(["lake", "env", "lean", str(audit.relative_to(LEAN))],
                         cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
    output = run.stdout + run.stderr
    (results / "tier5_audit.log").write_text(output, encoding="utf-8")
    reports = parse_reports(output)
    unchanged = hashes == {str(p.relative_to(ROOT)).replace("\\", "/"): sha(p) for p in paths}
    unchanged = unchanged and locked == check_locks(manifest)
    unchanged = unchanged and set(paths) == set(SOURCE.glob("*.lean"))
    ok = valid_audit(run.returncode, reports, expected, unchanged)
    complete = ok and not pending
    status = {"valid": ok, "complete": complete, "audit_exit_code": run.returncode,
        "target_count": len(targets), "proved_targets": [t["theorem"] for t in available] if ok else [],
        "pending_targets": pending, "root_count": len(reports), "expected_root_count": len(expected),
        "sources_unchanged_during_audit": unchanged, "locked_sha256": locked,
        "source_sha256": hashes, "reports": reports}
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(f"Tier 5 audit: valid={ok}, complete={complete}, targets={len(available)}/{len(targets)}, "
          f"roots={len(reports)}/{len(expected)}")
    return 0 if ok and (complete or not args.require_complete) else 1


if __name__ == "__main__":
    raise SystemExit(main())
