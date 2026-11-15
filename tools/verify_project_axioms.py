"""Build every Lean module and audit the axioms of every project constant.

The per-result audits check hand-registered theorems, and each one builds only
the modules it names. This audit registers nothing. It

1. builds every module under lean/ThresholdHC, so a file that no verifier
   names still has to compile;
2. imports all of them at once and asks the environment for every constant
   they declare;
3. fails unless no project module declares an axiom and every constant
   depends only on propext, Classical.choice and Quot.sound.

It also reads, from the same environment,

4. every instance a project module exports, scoped ones included, and fails
   unless each is a named project constant at the default priority in the
   global scope, and no data-carrying instance on types the project does not
   define is new (an instance such as `LE ℝ` would change what a restated
   statement means once its module is imported);
5. a fingerprint of every project definition and inductive type, with proofs
   erased, and compares it with the definition lock `tools/definition_lock.json`.
   A changed or removed definition is an error, so the definitions behind a
   restated statement cannot change while its proofs are adjusted. A new
   definition is an error until it is added with `--add-definitions`, which
   never changes an existing entry.

With --replay-main-theorem it also replays, through the toolchain's independent
kernel checker, every project module in the import closure of both halves of
the main RMS law. `#print axioms` cannot see a declaration that skipped the
kernel; the replay can.

The audit prints its report and, only with --add-definitions, adds new entries
to the definition lock. It complements the exact-type audits and does not
replace them: the lock pins what the definitions are, not what they mean.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess

from verify_blind_upper_components import LEAN, ROOT, SORRY_WARNING, imports, strip_comments

ALLOWED = ("propext", "Classical.choice", "Quot.sound")
MAIN_THEOREM = ("ThresholdHC.Tier6.Full", "ThresholdHC.BlindUpper.Full")
FIELD = re.compile(r"PROJECT_AXIOMS (\w+)=(.*)$", re.M)
INSTANCE = re.compile(r"^PROJECT_INSTANCE (\S+) (\S+) (\d+) (prop|data|orphan)$", re.M)
DEFINITION_COUNT = re.compile(r"^PROJECT_DEFINITIONS count=(\d+)$", re.M)
DEFINITION = re.compile(r"^PROJECT_DEFINITION (\S+) ([0-9:]+)$", re.M)
DEFINITION_LOCK = ROOT / "tools/definition_lock.json"
DEFAULT_PRIORITY = 1000
# Data-carrying instances on types the project does not define. Each one
# changes how every importing module elaborates those types, so the list is
# closed: a new one is an error. All six put the discrete sigma-algebra `⊤` on
# a countable type of tape symbols, actions or words, as the models require.
ORPHAN_INSTANCES = frozenset({
    "ThresholdHC.Tier4.tapeSymbolMeasurableSpace",
    "ThresholdHC.Tier5.creationActionMeasurableSpace",
    "ThresholdHC.BlindUpper.boolListMeasurableSpace",
    "ThresholdHC.OracleLower.selectedRequestMeasurableSpace",
    "ThresholdHC.RareAboveTwo.boolWordsMeasurableSpace",
    "ThresholdHC.CriticalUpper.boolWordsMeasurableSpace",
})
# Runs after the imports. It lives here, not under lean/, because the project
# sources may not define commands.
COMMAND = """
open Lean Elab Command in
elab "#project_axioms" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let allowed : NameSet :=
    ({} : NameSet).insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  let mut constants : Nat := 0
  let mut theorems : Nat := 0
  let mut declared : Array Name := #[]
  let mut offenders : Array Name := #[]
  let mut used : NameSet := {}
  for (c, info) in env.constants.map₁.toList do
    match env.getModuleIdxFor? c with
    | some idx =>
      if (`ThresholdHC).isPrefixOf mods[idx.toNat]! then
        constants := constants + 1
        match info with
        | .thmInfo _ => theorems := theorems + 1
        | .axiomInfo _ => declared := declared.push c
        | _ => pure ()
        let axioms ← collectAxioms c
        for a in axioms do
          used := used.insert a
        if axioms.any (fun a => !allowed.contains a) then offenders := offenders.push c
    | none => pure ()
  let project := (mods.filter fun m => (`ThresholdHC).isPrefixOf m).size
  logInfo m!"PROJECT_AXIOMS modules={project}"
  logInfo m!"PROJECT_AXIOMS constants={constants}"
  logInfo m!"PROJECT_AXIOMS theorems={theorems}"
  logInfo m!"PROJECT_AXIOMS declared={declared.qsort Name.lt}"
  logInfo m!"PROJECT_AXIOMS used={used.toArray.qsort Name.lt}"
  logInfo m!"PROJECT_AXIOMS offenders={offenders.qsort Name.lt}"

open Lean Elab Command Meta in
elab "#project_definitions" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let project (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some idx => (`ThresholdHC).isPrefixOf mods[idx.toNat]!
    | none => false
  -- Every instance a project module exports, scoped instances included.
  for i in [0:mods.size] do
    if (`ThresholdHC).isPrefixOf mods[i]! then
      for entry in instanceExtension.ext.getModuleEntries env (show ModuleIdx from i) do
        let (scope, e) := match entry with
          | .global e => ("global", e)
          | .scoped ns e => (s!"scoped:{ns}", e)
        let kind ← liftTermElabM do
          let ty ← inferType e.val
          if ← isProp ty then
            return "prop"
          let body ← forallTelescopeReducing ty fun _ b => pure b
          return if body.getUsedConstants.any project then "data" else "orphan"
        logInfo m!"PROJECT_INSTANCE {e.globalName?.getD .anonymous} {scope} {e.priority} {kind}"
  -- A fingerprint of every definition and inductive type, with proofs erased,
  -- and of the matchers and auxiliary definitions they use. Matchers and the
  -- auxiliary definitions of a theorem's proof are not roots, so a proof can
  -- change without changing the lock.
  let erase (e : Expr) : MetaM Expr :=
    Meta.transform e (pre := fun s => do
      if ← isProof s then return .done (.const ``True.intro []) else return .continue)
  let ofTheorem (c : Name) : Bool := Id.run do
    let mut p := c.getPrefix
    while !p.isAnonymous do
      if let some (.thmInfo _) := env.find? p then
        return true
      p := p.getPrefix
    return false
  let mut pending : Array Name := #[]
  for (c, info) in env.constants.map₁.toList do
    if project c && !ofTheorem c then
      match info with
      | .defnInfo _ => if !isMatcherCore env c then pending := pending.push c
      | .inductInfo _ => pending := pending.push c
      | _ => pure ()
  let mut seen : NameSet := {}
  let mut out : Array (Name × String) := #[]
  while !pending.isEmpty do
    let c := pending.back!
    pending := pending.pop
    if seen.contains c then continue
    seen := seen.insert c
    let mut parts : Array Expr := #[]
    match env.find? c with
    | some (.defnInfo d) =>
      parts := #[← liftTermElabM (erase d.type), ← liftTermElabM (erase d.value)]
    | some (.inductInfo d) =>
      parts := #[← liftTermElabM (erase d.type)]
      for ctor in d.ctors do
        if let some ci := env.find? ctor then
          parts := parts.push (← liftTermElabM (erase ci.type))
    | _ => continue
    out := out.push (c, ":".intercalate (parts.toList.map fun p => toString (toString p).hash))
    for p in parts do
      for n in p.getUsedConstants do
        if project n && !seen.contains n then pending := pending.push n
  logInfo m!"PROJECT_DEFINITIONS count={out.size}"
  for (c, f) in out.qsort (fun a b => a.1.lt b.1) do
    logInfo m!"PROJECT_DEFINITION {c} {f}"

#project_axioms
#project_definitions
"""


def project_modules(root: Path = LEAN) -> list[str]:
    """Every project source, by module name: the root file and all of ThresholdHC/."""
    paths = [root / "ThresholdHC.lean", *sorted((root / "ThresholdHC").rglob("*.lean"))]
    modules = [path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
               for path in paths if path.is_file()]
    if len(modules) != len(set(modules)) or "ThresholdHC" not in modules:
        raise ValueError("Duplicate or missing project module")
    return modules


def audit_source(modules: list[str]) -> str:
    return "".join(f"import {module}\n" for module in modules) + COMMAND


def names(text: str) -> list[str]:
    inner = text.strip()
    if not (inner.startswith("[") and inner.endswith("]")):
        raise ValueError("Malformed name list in the project axiom report: " + text)
    return [name.strip() for name in inner[1:-1].split(",") if name.strip()]


def validate_report(output: str, returncode: int, modules: int) -> dict:
    """Read the six report lines and reject anything but a clean, complete audit."""
    if returncode:
        raise ValueError("Project axiom audit exited unsuccessfully")
    if SORRY_WARNING.search(output):
        raise ValueError("Project axiom audit reported a declaration that uses sorry")
    fields: dict[str, str] = {}
    for key, value in FIELD.findall(output):
        if key in fields:
            raise ValueError("Duplicate project axiom report line: " + key)
        fields[key] = value
    expected = {"modules", "constants", "theorems", "declared", "used", "offenders"}
    if set(fields) != expected:
        raise ValueError("Missing or unexpected project axiom report lines")
    counts = {}
    for key in ("modules", "constants", "theorems"):
        if not fields[key].strip().isdigit():
            raise ValueError("Malformed count in the project axiom report: " + key)
        counts[key] = int(fields[key])
    if counts["modules"] != modules:
        raise ValueError(f"Audited {counts['modules']} project modules, expected {modules}")
    if not 0 < counts["theorems"] <= counts["constants"]:
        raise ValueError("Project axiom audit saw no project theorems")
    declared, used, offenders = (names(fields[key]) for key in ("declared", "used", "offenders"))
    if declared:
        raise ValueError("Project modules declare axioms: " + ", ".join(declared))
    if offenders:
        raise ValueError("Constants with disallowed axioms: " + ", ".join(offenders))
    if set(used) - set(ALLOWED):
        raise ValueError("Disallowed transitive axiom: " + ", ".join(sorted(set(used) - set(ALLOWED))))
    return {**counts, "used": used}


def validate_instances(output: str) -> list[tuple[str, str]]:
    """Every exported project instance: named, global, default priority, no new orphan."""
    found = INSTANCE.findall(output)
    if not found:
        raise ValueError("The project instance report is missing")
    for name, scope, priority, kind in found:
        if not name.startswith("ThresholdHC."):
            raise ValueError("Instance on a constant outside the project: " + name)
        if scope != "global":
            raise ValueError(f"Scoped project instance {name} ({scope})")
        if int(priority) != DEFAULT_PRIORITY:
            raise ValueError(f"Project instance {name} has priority {priority}")
        if kind == "orphan" and name not in ORPHAN_INSTANCES:
            raise ValueError("New data-carrying instance on a type the project does not define: "
                             + name)
    orphans = {name for name, _, _, kind in found if kind == "orphan"}
    if orphans != ORPHAN_INSTANCES:
        raise ValueError("Registered orphan instance missing: "
                         + ", ".join(sorted(ORPHAN_INSTANCES - orphans)))
    return [(name, kind) for name, _, _, kind in found]


def definition_fingerprints(output: str) -> dict[str, str]:
    counts = DEFINITION_COUNT.findall(output)
    found = DEFINITION.findall(output)
    if len(counts) != 1 or int(counts[0]) != len(found) or not found:
        raise ValueError("Missing or incomplete definition fingerprints")
    fingerprints: dict[str, str] = {}
    for name, fingerprint in found:
        if name in fingerprints:
            raise ValueError("Duplicate definition fingerprint: " + name)
        fingerprints[name] = fingerprint
    return fingerprints


def read_lock(path: Path) -> dict:
    lock = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(lock.get("definitions"), dict):
        raise ValueError("Malformed definition lock")
    return lock


def compare_definitions(locked: dict[str, str], actual: dict[str, str]) -> list[str]:
    """Fail on a changed or removed definition; return the new ones."""
    changed = sorted(name for name in locked if name in actual and actual[name] != locked[name])
    removed = sorted(name for name in locked if name not in actual)
    if changed:
        raise ValueError("Locked definitions changed: " + ", ".join(changed))
    if removed:
        raise ValueError("Locked definitions removed: " + ", ".join(removed))
    return sorted(name for name in actual if name not in locked)


def add_definitions(path: Path, lock: dict, actual: dict[str, str], new: list[str]) -> None:
    """Add entries for new definitions only. Existing entries are never rewritten."""
    definitions = dict(lock["definitions"])
    definitions.update({name: actual[name] for name in new})
    lock = {**lock, "definitions": dict(sorted(definitions.items()))}
    lock.setdefault("added", []).append({
        "at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "count": len(new),
    })
    path.write_text(json.dumps(lock, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def check_build(output: str, returncode: int) -> None:
    if returncode:
        raise ValueError("Building every project module failed")
    if SORRY_WARNING.search(output):
        raise ValueError("A project module uses sorry")


def import_closure(roots: tuple[str, ...], root: Path = LEAN) -> list[str]:
    """Project modules reachable from the given modules, themselves included."""
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        path = root / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise ValueError("Missing project module: " + module)
        seen.add(module)
        source = strip_comments(path.read_text(encoding="utf-8"))
        # Fails closed on an import line it cannot read, so no module is skipped.
        stack.extend(name for name in imports(source)
                     if name == "ThresholdHC" or name.startswith("ThresholdHC."))
    return sorted(seen)


def kernel_checker(lake: str) -> Path:
    sysroot = subprocess.run([lake, "env", "printenv", "LEAN_SYSROOT"], cwd=LEAN, check=True,
                             capture_output=True, text=True, encoding="utf-8").stdout.strip()
    checker = Path(sysroot) / "bin" / "leanchecker"
    if not sysroot or not checker.is_file():
        raise ValueError("The pinned toolchain has no leanchecker")
    return checker


def replay(modules: list[str], lake: str, jobs: int) -> None:
    """One checker process per module: a process that replays many keeps them all in memory."""
    checker = str(kernel_checker(lake))

    def one(module: str) -> tuple[str, int, str]:
        run = subprocess.run([lake, "env", checker, module], cwd=LEAN, capture_output=True,
                             text=True, encoding="utf-8")
        return module, run.returncode, (run.stdout + run.stderr).strip()

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        failed = [(module, output) for module, code, output in pool.map(one, modules) if code]
    if failed:
        for module, output in failed:
            print(f"{module}: {output}")
        raise ValueError(f"Kernel replay failed for {len(failed)} of {len(modules)} modules")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--no-build", action="store_true",
                        help="audit the modules as already built; a missing object is an error")
    parser.add_argument("--replay-main-theorem", action="store_true",
                        help="also replay the main RMS law's project modules through leanchecker")
    parser.add_argument("--jobs", type=int, default=2, help="parallel kernel replays")
    parser.add_argument("--definition-lock", type=Path, default=DEFINITION_LOCK)
    parser.add_argument("--add-definitions", action="store_true",
                        help="add lock entries for new definitions; existing entries never change")
    args = parser.parse_args()
    lock = read_lock(args.definition_lock)
    modules = project_modules()
    if not args.no_build:
        build = subprocess.run([args.lake, "build", *modules], cwd=LEAN, capture_output=True,
                               text=True, encoding="utf-8")
        output = build.stdout + build.stderr
        if build.returncode:
            print(output[-4000:], end="")
        check_build(output, build.returncode)
        print(f"Built {len(modules)} project modules")
    run = subprocess.run([args.lake, "env", "lean", "--stdin"], cwd=LEAN,
                         input=audit_source(modules), capture_output=True, text=True,
                         encoding="utf-8")
    output = run.stdout + run.stderr
    print(output, end="")
    report = validate_report(output, run.returncode, len(modules))
    print(f"Verified {report['constants']} constants ({report['theorems']} theorems) in "
          f"{report['modules']} modules: axioms {', '.join(report['used'])}")
    instances = validate_instances(output)
    print(f"Verified {len(instances)} exported project instances: named, global, default "
          f"priority, {len(ORPHAN_INSTANCES)} registered orphans")
    actual = definition_fingerprints(output)
    new = compare_definitions(lock["definitions"], actual)
    if new and not args.add_definitions:
        raise ValueError(f"{len(new)} definitions are not in the definition lock: "
                         + ", ".join(new[:20]) + (" ..." if len(new) > 20 else "")
                         + ". Add them with --add-definitions.")
    if new:
        add_definitions(args.definition_lock, lock, actual, new)
        print(f"Added {len(new)} new definitions to {args.definition_lock}")
    print(f"Verified {len(actual) - len(new)} locked definition fingerprints")
    if args.replay_main_theorem:
        closure = import_closure(MAIN_THEOREM)
        replay(closure, args.lake, max(1, args.jobs))
        print(f"Replayed {len(closure)} main-theorem modules through the kernel checker")


if __name__ == "__main__":
    main()
