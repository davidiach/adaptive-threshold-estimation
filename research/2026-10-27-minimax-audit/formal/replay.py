"""Current-source Lean replay; all reports stay in this new research directory.

This is an additional audit, not a replacement for frozen validators. It calls
their read-only lock, declaration, and axiom validators; builds current modules
through Lake; and checks every registered exact type in a new audit source.
Build caches may be updated, but no historical source, lock, or report is edited.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / "lean"
sys.path.insert(0, str(ROOT / "tools"))
import score
import verify_tier3 as tier3
import verify_tier4 as tier4
import verify_uniform713 as u713

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    env = dict(os.environ, PYTHONUTF8="1", ELAN_HOME=str(ROOT / ".runtime/elan"))
    env["PATH"] = str(ROOT / ".runtime/elan/bin") + os.pathsep + env.get("PATH", "")
    record = {"valid": False, "commands": [], "head": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()}
    def save():
        (HERE / "replay.json").write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8")
    def run(command, name):
        if command[0] == "lake":
            command = [str(ROOT / ".runtime/elan/bin/lake.exe"), *command[1:]]
        started = time.time()
        result = subprocess.run(command, cwd=LEAN, env=env, capture_output=True,
                                text=True, encoding="utf-8", timeout=900)
        (HERE / (name+".log")).write_text(result.stdout+result.stderr, encoding="utf-8")
        record["commands"].append({"command": command, "cwd": str(LEAN),
            "exit_code": result.returncode, "seconds": time.time()-started,
            "log": name+".log"})
        save()
        if result.returncode:
            raise RuntimeError(f"Failed: {command}; see {name}.log")
        return result.stdout+result.stderr
    save()
    record["lean_version"] = run(["lake", "env", "lean", "--version"], "version").strip()
    frozen_ok, frozen_errors = score.check_frozen()
    if not frozen_ok:
        raise RuntimeError(frozen_errors)
    forbidden = score.scan_forbidden()
    if forbidden:
        raise RuntimeError(forbidden)
    modules = set()
    lines = []
    expected = set()
    counts = {}
    locked = {}
    for tool, name in [(tier3, "tier3"), (tier4, "tier4")]:
        manifest = json.loads((ROOT / tool.MANIFEST).read_text())
        locked.update(tool.check_locks(manifest))
        sources = sorted(tool.SOURCE.glob("*.lean"))
        roots = [r for p in sources for r in tool.declarations(p)]
        targets = manifest["targets"]
        if any(t["theorem"] not in roots for t in targets):
            raise RuntimeError("Incomplete target list: " + name)
        for p in sources:
            modules.add(".".join(p.relative_to(LEAN).with_suffix("").parts))
        expected.update(roots)
        for target in targets:
            root = "MinimaxReplay."+name+"_"+target["theorem"].rsplit(".",1)[1]
            lines.append(f"theorem {root} : {target['statement']} := {target['theorem']}")
            expected.add(root)
        counts[name] = {"targets": len(targets), "roots_including_exact_types": len(roots)+len(targets)}
    manifest = json.loads((ROOT / "tools/uniform713_targets.json").read_text())
    locked.update(u713.check_specification_lock(manifest))
    for module, roots in manifest["modules"].items():
        modules.add(module)
        source = tier3.strip_comments((LEAN / (module.replace(".","/")+".lean")).read_text(encoding="utf-8"))
        if tier3.FORBIDDEN.search(source):
            raise RuntimeError("Forbidden proof escape: " + module)
        declared = re.findall(r"^(?:@\[[^\]]+\]\s+)?(?:theorem|lemma|instance)\s+([\w']+)", source, re.M)
        namespaces = re.findall(r"^namespace\s+([\w.]+)", source, re.M)
        actual = {namespaces[0]+"."+n for n in declared} if declared else set()
        if actual != set(roots):
            raise RuntimeError("713 root registration mismatch: " + module)
        expected.update(roots)
    lines.append(f"example : ThresholdHC.Uniform713.FullBound713Statement := {manifest['full_theorem']}")
    counts["uniform713"] = {"registered_roots": sum(len(x) for x in manifest["modules"].values()), "full_exact_type": True}
    for target in score.TARGETS["targets"]:
        modules.add(".".join(Path(target["file"]).relative_to("lean").with_suffix("").parts))
        root = "MinimaxReplay.scored_"+target["name"]
        lines.append(f"theorem {root} : {score.TARGETS['namespace_targets']}.{target['name']} := {score.TARGETS['namespace_proofs']}.{target['name']}")
        expected.add(root)
    counts["scored"] = {"exact_type_roots": len(score.TARGETS["targets"])}
    bridge = LEAN / "ThresholdHC/ResearchRouteA"
    spec = importlib.util.spec_from_file_location("route_a_replay", bridge / "verify.py")
    bridge_tool = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bridge_tool)
    lock = json.loads((bridge / "SPEC_LOCK_v1.json").read_text())
    closure = {str(p.relative_to(ROOT)).replace("\\","/") for p in bridge_tool.closure([bridge / "SeparateBoundsSpec.lean"])}
    if closure != set(lock["specification_closure"]):
        raise RuntimeError("Route A specification closure mismatch")
    locked.update(lock["locked_sha256"])
    modules.add("ThresholdHC.ResearchRouteA.Sanity")
    expected.update(bridge_tool.TARGETS)
    lines += ["example : ThresholdHC.ResearchRouteA.SeparateMomentBoundsStatement := ThresholdHC.ResearchRouteA.separate_moment_bounds",
              "example : ThresholdHC.ResearchRouteA.UniformFamilyBoundsStatement := ThresholdHC.ResearchRouteA.uniform_family_bounds"]
    counts["route_a"] = {"registered_roots": len(bridge_tool.TARGETS), "exact_types": 2}
    for rel, digest in locked.items():
        if sha(ROOT / rel) != digest:
            raise RuntimeError("Lock mismatch: " + rel)
    snapshots = {str(p.relative_to(ROOT)).replace("\\","/"): sha(p)
                 for p in (LEAN / "ThresholdHC").rglob("*.lean")}
    audit = HERE / "CurrentSourceAudit.lean"
    audit.write_text("\n".join(["import "+m for m in sorted(modules)] + lines +
                    ["#print axioms "+r for r in sorted(expected)])+"\n", encoding="utf-8")
    record.update(source_sha256=snapshots, locked_sha256=locked, counts=counts,
                  audit_source_sha256=sha(audit), expected_roots=len(expected))
    save()
    # Sequential module invocations avoid unconstrained parallel build jobs.
    for index, module in enumerate(sorted(modules)):
        print(f"build {index+1}/{len(modules)} {module}", flush=True)
        run(["lake", "build", module], f"build_{index+1:02d}")
    output = run(["lake", "env", "lean", str(audit)], "current_source_audit")
    reports = tier3.parse_reports(output)
    unchanged = all(sha(ROOT / rel)==digest for rel,digest in snapshots.items())
    locks_unchanged = all(sha(ROOT / rel)==digest for rel,digest in locked.items())
    ok = tier3.valid_audit(0, reports, expected, unchanged and locks_unchanged)
    record.update(valid=ok, complete=ok, reports=reports, actual_roots=len(reports),
                  sources_unchanged=unchanged, locks_unchanged=locks_unchanged,
                  axiom_union=sorted(set(a for xs in reports.values() for a in xs)))
    save()
    print(json.dumps({k:record[k] for k in ["valid","complete","actual_roots","expected_roots","axiom_union"]}), flush=True)
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
