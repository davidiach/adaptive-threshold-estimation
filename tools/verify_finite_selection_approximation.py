"""Audit the assembled finite-law approximation and original-objective certificate.

The mathematical scheme and extension count are checked. Polynomial bit
complexity and execution of numerical oracles/Python remain separate boundaries.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, ROOT, project_dependencies, registered_names, sha,
    strip_comments, validate_reports,
)

PREFIX = "ThresholdHC.FiniteSelectionApproximation."
SOURCES = LEAN / "ThresholdHC/FiniteSelectionApproximation"
LOCK = SOURCES / "SPECIFICATION.json"
MODULES = ("Bins", "Parameters", "Traces", "States", "Compression", "Frontier",
           "Endpoints", "Menus", "Objective", "Specification", "Full")
TARGETS = {"finite_law_approximation": "FiniteLawApproximationStatement"}
EXACT_COUNT = 12
SCOPE = ("Finite-law original-K approximation with certified rational endpoints, finite "
         "precision, concrete dyadic keys, every-stage state count and Q*S extensions. "
         "All finite probability laws, including rational finite laws. No polynomial "
         "bit-complexity or numerical/Python execution claim.")

EXACT = """
example (r : ℝ) (M : ℕ) (hr : 0 < r) (hM : 0 < M) :
    ValidBins (1+1/(M:ℝ)) (binKey r M) := binKey_valid hr hM

example (r x : ℚ) (M : ℕ) : rationalKey r M x = binKey (r:ℝ) M (x:ℝ) :=
  rationalKey_cast r x M

example : rationalKey (1/4) 2 0 = none := by decide
example : rationalKey (1/4) 2 (3/8) = some (0,1) := by norm_num [rationalKey, Int.log]
example : rationalKey (1/4) 2 (1/16) = some (-2,0) := by norm_num [rationalKey, Int.log]

example (m n : ℕ) (R ε : ℝ) (hm : 0 < m) (hn : n ≤ m) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let L := 4+(⌈Real.logb 2 R⌉₊:ℝ)
    let M := ⌈16*(m:ℝ)*L/ε⌉₊
    let η := (1+1/(M:ℝ))^n-1
    0 ≤ η ∧ η ≤ 1 ∧ L*η ≤ ε/8 := compression_error hm hn hε hε1

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    (ρ B : ℝ) (hρ : 0 < ρ) (hB : 0 < B) (xs : List (Finset Gap))
    (hx : xs ∈ enumerate (lawMenus μ hF)) :
    min ρ (min (Real.sqrt (ρ*minCost (cost μ) (lawMenus μ hF)/B))
      (min 1 (2/Real.sqrt B))) ≤ menuObjective μ ρ B xs :=
  menuObjective_floor μ hF hρ hB hx

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite) :
    ((lawMenus μ hF).map Finset.card).sum ≤ hF.toFinset.card+(occupiedBands hF.toFinset).length :=
  lawMenus_option_count μ hF

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    (ρ B ε : ℝ) (hρ : 0 < ρ) (hρu : ρ ≤ 1/4) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ ys ∈ lawFrontier μ hF B ε, ys ∈ enumerate (lawMenus μ hF) ∧
      menuObjective μ ρ B ys ≤ (1+ε/4)*(selection μ ρ B).toReal :=
  finite_law_near_optimal μ hF hρ hρu hB hε hε1

example {α : Type*} (F : Finset α) (hne : F.Nonempty) (J : α → ℝ)
    (d b : ℝ) (hd : 0 < d) (hb : 1 < b) (hlower : ∀ x ∈ F, d ≤ J x) :
    ∃ N ≤ ⌈(b+1)/((b-1)*d)⌉₊+1,
      (upperEndpoint N (J (upperWitness F hne J N)):ℝ) ≤ b*(leastLower F hne J N:ℝ) :=
  refinement_terminates F hne J hd hb hlower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    (ρ B ε : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < ε → ε ≤ 1 →
    let ms := lawMenus μ hF
    let r := minCost (cost μ) ms
    let R := maxCost (cost μ) ms/r
    let L := 4+(⌈Real.logb 2 R⌉₊:ℝ)
    let M := ⌈16*(ms.length:ℝ)*L/ε⌉₊
    let S := 1+M^2*(1+⌊Real.logb 2 R⌋₊)*(1+⌊Real.logb 2 (L*R)⌋₊)
    let Q := hF.toFinset.card+(occupiedBands hF.toFinset).length
    let J := menuObjective μ ρ B
    let K := (selection μ ρ B).toReal
    ∃ N ≤ sufficientPrecision (positiveFloor ρ B r) (1+ε/4),
      ∃ xs ∈ lawFrontier μ hF B ε, ∃ l u : ℚ,
        traceSet xs ∈ suffixChoices hF.toFinset ∧
        ENNReal.ofReal (J xs) = min (ENNReal.ofReal ρ)
          (selectionObjective μ ρ B (μ.restrict (traceSet xs))) ∧
        u = upperEndpoint N (J xs) ∧
        (∀ ys ∈ lawFrontier μ hF B ε, u ≤ upperEndpoint N (J ys)) ∧
        (∀ ys ∈ lawFrontier μ hF B ε, (l:ℝ) ≤ J ys) ∧
        0 < (l:ℝ) ∧ (l:ℝ)/(1+ε/4) ≤ K ∧ K ≤ J xs ∧ J xs ≤ (u:ℝ) ∧
        (u:ℝ) ≤ (1+ε)*((l:ℝ)/(1+ε/4)) ∧
        (∀ rest, rest.IsSuffix ms →
          (trimSolve (binKey r M) (cost μ) (summary (cost μ) r ε)
            (saving μ (1/Real.sqrt B)) rest).card ≤ S) ∧
        extensionCount (binKey r M) (cost μ) (summary (cost μ) r ε)
          (saving μ (1/Real.sqrt B)) ms ≤ Q*S :=
  finite_law_approximation
"""


def protected_sources() -> set[Path]:
    return project_dependencies([SOURCES / "Specification.lean"]) | {
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }


def validate_sources() -> set[str]:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected_sources())}
    if lock.get("sha256") != actual:
        raise ValueError("Changed finite-selection specification or locked dependency")
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing finite-selection module")
    paths = [SOURCES / (name+".lean") for name in MODULES]
    roots = set()
    for path in project_dependencies(paths):
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        if path in paths:
            for name in registered_names(source):
                root = PREFIX+name
                if root in roots:
                    raise ValueError("Duplicate declaration root: " + root)
                roots.add(root)
    required = {name for pair in TARGETS.items() for name in pair} | {
        "binKey_valid", "rationalKey_cast", "compression_error", "retained_entropy",
        "every_stage_card", "lawMenus_option_count", "menuObjective_floor",
        "refinement_terminates", "endpoint_certificate", "finite_law_near_optimal",
    }
    if not {PREFIX+name for name in required} <= roots:
        raise ValueError("Missing finite-selection audit target")
    return roots


def audit_input() -> tuple[str, set[str]]:
    roots = validate_sources()
    source = "\n".join([
        "import ThresholdHC.FiniteSelectionApproximation.Full",
        "open MeasureTheory ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix",
        "open ThresholdHC.GapLawMenus ThresholdHC.BandCostSelection ThresholdHC.SelectionApproximation",
        "open ThresholdHC.FiniteSelectionApproximation",
        "open scoped ENNReal Classical",
        *[f"example : {statement} := {theorem}" for theorem, statement in TARGETS.items()],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden proof escape in generated audit")
    return source, roots


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true", help="Use only after a complete current build")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    source, roots = audit_input()
    out = (args.output_dir or ROOT / ".runtime/finite-selection" /
           datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "audit.lean").write_text(source, encoding="utf-8")
    if not args.no_build:
        with (out / "build.log").open("w", encoding="utf-8") as log:
            subprocess.run(["lake", "build", PREFIX+"Full"], cwd=LEAN, check=True,
                           stdout=log, stderr=subprocess.STDOUT)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    report = run.stdout+run.stderr
    (out / "audit.log").write_text(report, encoding="utf-8")
    print(report, end="")
    validate_reports(report, run.returncode, roots)
    compiler_version = subprocess.check_output(["lake", "env", "lean", "--version"],
                                              cwd=LEAN, text=True, encoding="utf-8").strip()
    compiler_prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                                  cwd=LEAN, text=True, encoding="utf-8").strip())
    compiler = compiler_prefix / "bin" / ("lean.exe" if (compiler_prefix / "bin/lean.exe").exists() else "lean")
    pinned = (LEAN / "lean-toolchain").read_text(encoding="utf-8").strip().split(":v")[-1]
    if "version "+pinned+"," not in compiler_version:
        raise ValueError("Compiler differs from pinned toolchain")
    closure = project_dependencies([SOURCES / "Full.lean"])
    inputs = closure | {LOCK, Path(__file__).resolve(), ROOT / "tools/verify_blind_upper_components.py",
                       ROOT / "tools/verify_tier6.py", LEAN / "lean-toolchain",
                       LEAN / "lake-manifest.json", LEAN / "lakefile.toml"}
    def command(*cmd: str) -> str:
        return subprocess.check_output(cmd, cwd=ROOT, text=True, encoding="utf-8").strip()
    status = dict(valid=True, scope=SCOPE, proof_commit=command("git", "rev-parse", "HEAD"),
                  worktree_status=command("git", "status", "--porcelain"),
                  exact_statements=EXACT_COUNT, transitive_reports=len(roots),
                  allowed_axioms=["propext", "Classical.choice", "Quot.sound"],
                  mathematical_approximation_verified=True, bit_complexity_verified=False,
                  numerical_oracle_execution_verified=False, python_execution_verified=False,
                  project_source_closure=len(closure), build_skipped=args.no_build,
                  compiler=dict(version=compiler_version, path=str(compiler), sha256=sha(compiler)),
                  external_compiled_cache_trusted=True,
                  source_sha256={p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(inputs)},
                  audit_sha256=sha(out / "audit.lean"), report_sha256=sha(out / "audit.log"))
    (out / "status.json").write_text(json.dumps(status, indent=2)+"\n", encoding="utf-8")
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    print("Evidence:", out)


if __name__ == "__main__":
    main()
