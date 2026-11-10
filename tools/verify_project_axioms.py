"""Build every Lean module and audit the axioms of every project constant.

The per-result audits check hand-registered theorems, and each one builds only
the modules it names. This audit registers nothing. It

1. builds every module under lean/ThresholdHC, so a file that no verifier
   names still has to compile;
2. imports all of them at once and asks the environment for every constant
   they declare;
3. fails unless no project module declares an axiom and every constant
   depends only on propext, Classical.choice and Quot.sound.

With --replay-main-theorem it also replays, through the toolchain's independent
kernel checker, every project module in the import closure of both halves of
the main RMS law. `#print axioms` cannot see a declaration that skipped the
kernel; the replay can.

The audit prints its report and writes nothing. It complements the exact-type
audits and does not replace them: it says nothing about what a statement means.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess

from verify_blind_upper_components import IMPORT, LEAN, SORRY_WARNING, strip_comments

ALLOWED = ("propext", "Classical.choice", "Quot.sound")
MAIN_THEOREM = ("ThresholdHC.Tier6.Full", "ThresholdHC.BlindUpper.Full")
FIELD = re.compile(r"PROJECT_AXIOMS (\w+)=(.*)$", re.M)
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

#project_axioms
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
        stack.extend(name for name in IMPORT.findall(source)
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
    args = parser.parse_args()
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
    if args.replay_main_theorem:
        closure = import_closure(MAIN_THEOREM)
        replay(closure, args.lake, max(1, args.jobs))
        print(f"Replayed {len(closure)} main-theorem modules through the kernel checker")


if __name__ == "__main__":
    main()
