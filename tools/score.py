"""Lean-track scorer with anti-cheat checks.

Usage (from the kit root):
  python tools/score.py                 # build, audit, write results/lean_score.json
  python tools/score.py --accept PREV   # also decide accept/reject vs a previous score JSON
  python tools/score.py --no-build      # skip `lake build` (only if you just built)

A target counts as PROVEN only if all of the following hold:
  * FROZEN.sha256 matches (Statements.lean, targets, scorer, lake files, ...);
  * no forbidden constructs appear in any non-frozen Lean source;
  * `lake build` succeeds;
  * a freshly generated audit theorem `audit_<name> : ThresholdHC.Targets.<name>
    := ThresholdHC.Proofs.<name>` elaborates (so the type matches the frozen
    statement exactly);
  * `#print axioms audit_<name>` lists only propext, Classical.choice, Quot.sound.
`sorryAx` means unproved. Any other axiom is a VIOLATION.

v2 (Tier 2 approved, 27 Oct 2026): a run is valid only if the audit process
exits with status 0 and every target reports `proven` or `sorry` (this folds in
the independent guard Astra added in tools/verify_lean_checkpoint.py). Points
are also reported per tier.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
RESULTS = ROOT / "results"
TARGETS = json.loads((ROOT / "tools" / "targets.json").read_text())
ALLOWED = set(TARGETS["allowed_axioms"])

# Constructs that can bypass the kernel, fake output, or add assumptions.
FORBIDDEN = [
    (r"^\s*axiom\b", "axiom declaration"),
    (r"\bnative_decide\b", "native_decide (trusts compiled code)"),
    (r"implemented_by", "implemented_by"),
    (r"@\[\s*extern", "extern"),
    (r"\bunsafe\b", "unsafe"),
    (r"skipKernelTC", "kernel typecheck bypass"),
    (r"\bdebug\.", "debug option"),
    (r"^\s*opaque\b", "opaque constant"),
    (r"^\s*(?:local\s+|scoped\s+)?elab\b", "custom elaborator"),
    (r"^\s*(?:local\s+|scoped\s+)?macro(?:_rules)?\b", "macro"),
    (r"^\s*(?:local\s+|scoped\s+)?syntax\b", "syntax extension"),
    (r"\brun_cmd\b|\brun_elab\b|\brun_meta\b", "run_cmd/run_elab"),
    (r"^\s*initialize\b|^\s*builtin_initialize\b", "initialize"),
    (r"@\[\s*command_elab|@\[\s*term_elab|@\[\s*tactic\b", "elaborator attribute"),
    (r"#exit", "#exit"),
    (r"\bsorryAx\b", "explicit sorryAx"),
    (r"set_option\s+trust\b", "trust option"),
]


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check_frozen() -> tuple[bool, list[str]]:
    manifest = ROOT / "FROZEN.sha256"
    if not manifest.exists():
        return False, ["FROZEN.sha256 missing: Phase 0 not completed (run tools/freeze.py --init)"]
    problems = []
    for line in manifest.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        digest, rel = line.split(maxsplit=1)
        p = ROOT / rel
        if not p.exists():
            problems.append(f"frozen file missing: {rel}")
        elif sha256(p) != digest:
            problems.append(f"frozen file modified: {rel}")
    return not problems, problems


def scan_forbidden() -> list[str]:
    hits = []
    frozen = {LEAN / "ThresholdHC" / "Statements.lean", LEAN / "ThresholdHC" / "Statements2.lean"}
    for p in sorted(LEAN.rglob("*.lean")):
        if ".lake" in p.parts or p in frozen or ".audit" in p.parts:
            continue
        text = p.read_text(encoding="utf-8", errors="replace")
        # strip block and line comments so documentation does not trigger false hits
        stripped = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
        stripped = re.sub(r"--[^\n]*", "", stripped)
        for i, line in enumerate(stripped.splitlines(), 1):
            for pat, why in FORBIDDEN:
                if re.search(pat, line):
                    hits.append(f"{p.relative_to(ROOT)}:{i}: {why}: {line.strip()[:100]}")
    return hits


def run(cmd: list[str], timeout: int) -> tuple[int, str]:
    try:
        r = subprocess.run(cmd, cwd=LEAN, capture_output=True, text=True,
                           encoding="utf-8", timeout=timeout)
        return r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired as e:
        return 124, f"TIMEOUT after {timeout}s\n{e.stdout or ''}{e.stderr or ''}"
    except FileNotFoundError as e:
        return 127, f"command not found: {e}"


def write_audit() -> tuple[Path, dict[str, tuple[int, int]]]:
    ns_t, ns_p = TARGETS["namespace_targets"], TARGETS["namespace_proofs"]
    lines = ["import ThresholdHC", "", "namespace ThresholdHCAudit", ""]
    spans: dict[str, tuple[int, int]] = {}
    for t in TARGETS["targets"]:
        start = len(lines) + 1
        n = t["name"]
        lines.append(f"theorem audit_{n} : {ns_t}.{n} := {ns_p}.{n}")
        lines.append(f"#print axioms audit_{n}")
        lines.append("")
        spans[n] = (start, len(lines))
    lines += ["end ThresholdHCAudit", ""]
    d = LEAN / ".audit"
    d.mkdir(exist_ok=True)
    f = d / "Audit.lean"
    f.write_text("\n".join(lines))
    return f, spans


def parse_audit(output: str, spans: dict[str, tuple[int, int]]) -> dict[str, dict]:
    status = {n: {"status": "error", "axioms": None, "detail": "no axiom report"} for n in spans}
    pat = re.compile(r"'(?:ThresholdHCAudit\.)?audit_(\w+)'\s+(depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.S)
    for m in pat.finditer(output):
        n = m.group(1)
        if n not in status:
            continue
        axioms = [] if m.group(3) is None else [a.strip() for a in m.group(3).replace("\n", " ").split(",") if a.strip()]
        unexpected = set(axioms) - ALLOWED - {"sorryAx"}
        if unexpected:
            status[n] = {"status": "violation", "axioms": axioms, "detail": f"non-standard axioms {sorted(unexpected)}"}
        elif "sorryAx" in axioms:
            status[n] = {"status": "sorry", "axioms": axioms, "detail": "uses sorry"}
        else:
            status[n] = {"status": "proven", "axioms": axioms, "detail": ""}
    # any elaboration error inside a target's audit lines disqualifies it
    for m in re.finditer(r"Audit\.lean:(\d+):\d+:\s*error:?\s*(.*)", output):
        line = int(m.group(1))
        for n, (a, b) in spans.items():
            if a <= line <= b:
                status[n] = {"status": "error", "axioms": None, "detail": m.group(2)[:200]}
    return status


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--accept", type=Path, help="previous score JSON to compare against")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--timeout", type=int, default=7200)
    args = ap.parse_args()

    t0 = time.time()
    frozen_ok, frozen_problems = check_frozen()
    forbidden = scan_forbidden()
    build_ok, build_log = True, "skipped"
    if not args.no_build:
        rc, build_log = run(["lake", "build"], args.timeout)
        build_ok = rc == 0
    targets: dict[str, dict] = {}
    audit_log = ""
    audit_rc = None
    if build_ok:
        f, spans = write_audit()
        audit_rc, audit_log = run(["lake", "env", "lean", str(f.relative_to(LEAN))], args.timeout)
        targets = parse_audit(audit_log, spans)
    points_of = {t["name"]: t["points"] for t in TARGETS["targets"]}
    tier_of = {t["name"]: t.get("tier", 1) for t in TARGETS["targets"]}
    complete = bool(targets) and len(targets) == len(points_of) and all(
        s["status"] in {"proven", "sorry"} for s in targets.values())
    valid = frozen_ok and not forbidden and build_ok and audit_rc == 0 and complete
    proven = [n for n, s in targets.items() if s["status"] == "proven"] if valid else []
    violations = [n for n, s in targets.items() if s["status"] == "violation"]
    score = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "valid": valid and not violations,
        "frozen_ok": frozen_ok,
        "frozen_problems": frozen_problems,
        "forbidden": forbidden,
        "build_ok": build_ok,
        "audit_exit_code": audit_rc,
        "audit_complete": complete,
        "violations": violations,
        "points": sum(points_of[n] for n in proven) if not violations else 0,
        "max_points": sum(points_of.values()),
        "proven": sorted(proven),
        "points_by_tier": {str(k): {"points": sum(points_of[n] for n in proven if tier_of[n] == k),
                                    "max": sum(p for n, p in points_of.items() if tier_of[n] == k)}
                           for k in sorted(set(tier_of.values()))},
        "targets": targets,
        "seconds": round(time.time() - t0, 1),
    }
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "lean_score.json").write_text(json.dumps(score, indent=1))
    if not build_ok:
        (RESULTS / "lean_build.log").write_text(build_log[-200000:], encoding="utf-8")
    (RESULTS / "lean_audit.log").write_text(audit_log[-200000:], encoding="utf-8")

    print(f"valid={score['valid']} build_ok={build_ok} frozen_ok={frozen_ok} "
          f"audit_exit={audit_rc} complete={complete} "
          f"points={score['points']}/{score['max_points']} proven={len(proven)}/{len(points_of)} "
          + " ".join(f"tier{k}={v['points']}/{v['max']}" for k, v in score["points_by_tier"].items()))
    if build_ok and not complete:
        bad = [n for n, s in targets.items() if s["status"] not in {"proven", "sorry"}]
        print("  ! incomplete audit:", bad[:10])
    for p in frozen_problems + forbidden:
        print("  !", p)
    for n in violations:
        print("  VIOLATION:", n, targets[n]["detail"])
    if args.accept:
        prev = json.loads(args.accept.read_text())
        lost = sorted(set(prev.get("proven", [])) - set(proven))
        better = score["valid"] and score["points"] > prev.get("points", 0) and not lost
        print("ACCEPT" if better else "REJECT", f"(prev {prev.get('points', 0)} -> {score['points']}; lost={lost})")
        return 0 if better else 3
    return 0 if score["valid"] else 2


if __name__ == "__main__":
    sys.exit(main())
