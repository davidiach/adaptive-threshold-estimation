"""Rebuild and audit the two locked selection-approximation components.

Uses the pinned native Lean compiler and existing external package caches.
Every local dependency is freshly rebuilt into a new evidence directory.
No published record or project build artifact is overwritten.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, LEAN, ROOT, module_path, project_dependencies,
    sha, strip_comments, validate_reports,
)
from verify_entropy_tail_components import dependency_order

PREFIX = "ThresholdHC.SelectionApproximation."
SOURCE = LEAN / "ThresholdHC/SelectionApproximation"
LOCK = SOURCE / "SPECIFICATION.json"
MODULES = ("Model", "Entropy", "Compression")
EXACT_TARGETS = {
    PREFIX + "entropy_perturbation": PREFIX + "EntropyPerturbationStatement",
    PREFIX + "compression_invariant": PREFIX + "CompressionInvariantStatement",
}
SCOPE = (
    "Actual finite cost entropy perturbation from certified logarithmic summaries; "
    "feasible retained traces with no worse saving and two summaries within c^m, "
    "for any certified bin map. Includes derivative, surrogate, relative-error, "
    "zero-case and dyadic-cell lemmas. Not the full FPTAS, bit complexity, "
    "concrete bucket-index implementation, or Python execution."
)


def validate_sources() -> tuple[list[Path], set[str]]:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    protected = project_dependencies([SOURCE / "Model.lean"]) | {
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    if lock.get("sha256") != actual:
        raise ValueError("Locked specification, dependency or toolchain changed")
    paths = [module_path(PREFIX + name) for name in MODULES]
    if set(paths) != set(SOURCE.glob("*.lean")):
        raise ValueError("Missing or unregistered selection-approximation module")
    roots = []
    for path in project_dependencies(paths):
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        if path in paths:
            roots.extend(PREFIX + name for name in DECLARATION.findall(source))
    if len(roots) != len(set(roots)) or not set(EXACT_TARGETS) <= set(roots):
        raise ValueError("Duplicate or missing declaration root")
    return paths, set(roots)


def audit_source(roots: set[str]) -> str:
    return (
        "".join("import " + PREFIX + name + "\n" for name in MODULES)
        + "\n".join(f"example : {target} := {name}" for name, target in EXACT_TARGETS.items())
        + "\n\nopen ThresholdHC.SelectionApproximation\n"
        + "example : ValidBins 1 (fun x : ℝ => x) := validBins_identity\n"
        + "example : Close (1+1/(2:ℝ)) 1 (3/2) := by\n"
        + "  apply dyadic_cell_close (scale := 1) (M := 2) (j := 0) <;> norm_num\n\n"
        + "".join("#print axioms " + name + "\n" for name in sorted(roots))
    )


def checked_output(command: list[str], cwd: Path) -> str:
    return subprocess.check_output(command, cwd=cwd, text=True, encoding="utf-8").strip()


def package_libraries(cache: Path) -> tuple[list[Path], dict]:
    """Check each cached checkout's pinned commit and tracked source cleanliness.

    External compiled artifacts are trusted cache inputs, as in the existing
    project audits. This is not a rebuild of Mathlib or the Lean distribution.
    """
    manifest = json.loads((LEAN / "lake-manifest.json").read_text(encoding="utf-8"))
    libraries, records = [], {}
    for package in manifest["packages"]:
        checkout = cache / package["name"]
        revision = checked_output(["git", "rev-parse", "HEAD"], checkout)
        dirty = checked_output(["git", "status", "--porcelain", "--untracked-files=no"], checkout)
        if revision != package["rev"] or dirty:
            raise ValueError("External package differs from clean pinned checkout: " + package["name"])
        library = checkout / ".lake/build/lib/lean"
        if package["name"] == "mathlib" and not library.is_dir():
            raise ValueError("Missing external package build cache: " + str(library))
        # Tool-only packages (for example Cli) may have no library build.
        # A missing library actually imported by a proof is a compiler error.
        if library.is_dir():
            libraries.append(library)
        records[package["name"]] = dict(revision=revision,
                                       library=str(library) if library.is_dir() else None)
    return libraries, records


def reject_diagnostics(report: str, returncode: int) -> None:
    if returncode or re.search(r"\b(?:warning|error):", report):
        raise ValueError("Lean build or audit reported errors or warnings")


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-exe", default="lean", help="Pinned Lean executable, or elan's lean shim")
    parser.add_argument("--package-cache", type=Path, default=LEAN / ".lake/packages")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    paths, roots = validate_sources()
    ordered = dependency_order(paths)
    protected = set(ordered) | {
        LOCK, Path(__file__).resolve(), ROOT / "tools/verify_blind_upper_components.py",
        ROOT / "tools/verify_entropy_tail_components.py", ROOT / "tools/verify_tier6.py",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    libraries, packages = package_libraries(args.package_cache.resolve())
    version = checked_output([args.lean_exe, "--version"], LEAN)
    pinned_version = (LEAN / "lean-toolchain").read_text().strip().split(":v")[-1]
    if re.search(r"\bversion " + re.escape(pinned_version) + r"(?:,|\))", version) is None:
        raise ValueError("Compiler version differs from pinned toolchain: " + version)
    prefix = Path(checked_output([args.lean_exe, "--print-prefix"], LEAN))
    native = prefix / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    output = (args.output_dir or ROOT / ".runtime/selection-lean" / datetime.now(
        timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    output.mkdir(parents=True, exist_ok=False)
    objects = output / "objects"
    objects.mkdir()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [objects, *libraries])))
    status = dict(
        valid=False, scope=SCOPE, source_sha256=hashes, exact_targets=EXACT_TARGETS,
        compiler=dict(version=version, path=str(native), sha256=sha(native)),
        external_packages=packages, external_compiled_cache_trusted=True,
        exact_targets_checked=0, entropy_perturbation_verified=False,
        state_compression_verified=False, full_fptas_verified=False,
        python_execution_verified=False, commands=[], object_sha256={},
    )

    def save() -> None:
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    save()
    audit = output / "Audit.lean"
    audit.write_text(audit_source(roots), encoding="utf-8")
    if FORBIDDEN.search(strip_comments(audit.read_text(encoding="utf-8"))):
        raise ValueError("Forbidden proof escape in generated audit")
    commands = []
    for path in ordered:
        relative = path.relative_to(LEAN)
        obj = objects / relative.with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        commands.append(([str(native), "-j1", "-o", str(obj), str(relative)], obj))
    # Keep the compiler's module root explicit because the audit is outside lean/.
    commands.append(([str(native), "-j1", "-R", str(output), str(audit)], None))
    for i, (command, obj) in enumerate(commands, 1):
        result = subprocess.run(command, cwd=LEAN, env=env, capture_output=True,
                                text=True, encoding="utf-8", timeout=600)
        report = result.stdout + result.stderr
        (output / f"{i:03d}.log").write_text(report, encoding="utf-8")
        status["commands"].append(dict(command=command, exit_code=result.returncode))
        if obj is not None and obj.exists():
            status["object_sha256"][obj.relative_to(objects).as_posix()] = sha(obj)
        save()
        print(f"{i}/{len(commands)} {command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode or re.search(r"\b(?:warning|error):", report):
            print(report, flush=True)
        reject_diagnostics(report, result.returncode)
    status["axioms"] = validate_reports(report, result.returncode, roots)
    validate_sources()
    if any(sha(ROOT / name) != digest for name, digest in hashes.items()):
        raise ValueError("Protected source changed during audit")
    status.update(valid=True, audited_modules=len(paths), rebuilt_local_modules=len(ordered),
                  audited_declarations=len(roots), exact_targets_checked=len(EXACT_TARGETS),
                  concrete_checks=2, entropy_perturbation_verified=True,
                  state_compression_verified=True, audit_source_sha256=sha(audit))
    save()
    print(json.dumps(dict(valid=True, declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
