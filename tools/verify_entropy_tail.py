"""Check the entropy-tail formalization against its frozen target types.

The frozen specification fixes eight full target types for v6 Theorem 13.2.
Every registered target is checked for its exact type and transitive axioms.
The law is reported verified only when all eight are registered; use
--require-complete to fail otherwise.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess
import sys

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, module_path, project_dependencies, sha,
    strip_comments, validate_reports, imports, validate_dependency_freeze,
)
from verify_entropy_tail_components import dependency_order

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
SOURCE = LEAN / 'ThresholdHC/EntropyTail'
FREEZE = ROOT / 'tools/entropy_tail_specification_freeze.json'
MODULES = ('Model', 'Specification', 'Band', 'Entropy', 'Gamma', 'Objective', 'Bounds',
           'SingleAtom', 'Nonvacuity', 'Superadditive', 'HardSelection', 'Bridge', 'Upper', 'Lower', 'Law')
PREFIX = 'ThresholdHC.EntropyTail.'
FROZEN = {'lean/ThresholdHC/EntropyTail/Specification.lean': '8440d8853dd20cfcb4d0123fd30de0fae82ee970a0577f5e4ba0ebe041a1cbeb'}
TARGETS = {
    PREFIX+'entropy_tail_law': PREFIX+'EntropyTailLawStatement',
    PREFIX+'entropy_tail_upper': PREFIX+'EntropyTailUpperStatement',
    PREFIX+'entropy_tail_lower': PREFIX+'EntropyTailLowerStatement',
    PREFIX+'hard_selection': PREFIX+'HardSelectionStatement',
    PREFIX+'selection_bounds': PREFIX+'SelectionBoundsStatement',
    PREFIX+'single_atom': PREFIX+'SingleAtomStatement',
    PREFIX+'small_budget': PREFIX+'SmallBudgetStatement',
    PREFIX+'entropy_tail_nonvacuity': PREFIX+'EntropyTailNonvacuityStatement',
}
# Targets whose proofs are present. A target is proved only by its registered name.
PROVED = (PREFIX+'selection_bounds', PREFIX+'single_atom', PREFIX+'small_budget',
          PREFIX+'entropy_tail_nonvacuity', PREFIX+'hard_selection', PREFIX+'entropy_tail_upper',
          PREFIX+'entropy_tail_lower', PREFIX+'entropy_tail_law')
# Any declaration form of a target name, including modifiers such as `protected` and
# fully qualified names, which the shared root pattern does not report.
TARGET_DECLARATION = (r"\b(?:def|abbrev|structure|theorem|lemma|instance|inductive)\s+"
                      r"(?:_root_\.)?(?:" + re.escape(PREFIX) + r")?{}(?![\w'.])")
SCOPE = ('Entropy-tail law (v6 Theorem 13.2) in the observable rare-event experiment: '
         'universal two-sided comparison with the selection functional for every law on (0,1/2], '
         '0 < rho <= 1/4 and B > 0, the separate upper and lower halves, hard selections, '
         'the elementary bounds, the single-atom and small-budget values and nonvacuity. '
         'Budgets count actual flips and rarity is global.')


def exact_targets() -> dict[str, str]:
    return {name: TARGETS[name] for name in PROVED}


def validate_sources() -> tuple[list[Path], set[str]]:
    required_targets = {
        PREFIX+'entropy_tail_law': PREFIX+'EntropyTailLawStatement',
        PREFIX+'entropy_tail_upper': PREFIX+'EntropyTailUpperStatement',
        PREFIX+'entropy_tail_lower': PREFIX+'EntropyTailLowerStatement',
        PREFIX+'hard_selection': PREFIX+'HardSelectionStatement',
        PREFIX+'selection_bounds': PREFIX+'SelectionBoundsStatement',
        PREFIX+'single_atom': PREFIX+'SingleAtomStatement',
        PREFIX+'small_budget': PREFIX+'SmallBudgetStatement',
        PREFIX+'entropy_tail_nonvacuity': PREFIX+'EntropyTailNonvacuityStatement',
    }
    if TARGETS != required_targets:
        raise ValueError('Missing or changed exact full target')
    if len(PROVED) != len(set(PROVED)) or not set(PROVED) <= set(TARGETS):
        raise ValueError('Unknown or duplicate proved target')
    freeze = json.loads(FREEZE.read_text(encoding='utf-8'))
    if freeze['source_sha256'] != FROZEN or any(sha(ROOT/p) != h for p, h in FROZEN.items()):
        raise ValueError('Frozen entropy-tail specification changed')
    if freeze['targets'] != TARGETS:
        raise ValueError('Missing or changed exact full target')
    validate_dependency_freeze(SOURCE/'Specification.lean', freeze)
    paths = [module_path(PREFIX+m) for m in MODULES]
    if set(paths) != set(SOURCE.rglob('*.lean')):
        raise ValueError('Missing or unregistered entropy-tail module')
    for path in sorted(project_dependencies(paths) - set(paths)):
        if FORBIDDEN.search(strip_comments(path.read_text(encoding='utf-8'))):
            raise ValueError('Forbidden proof escape in imported module '+str(path))
    roots, seen, sources = [], set(), []
    all_modules = {PREFIX+m for m in MODULES}
    for path, name in zip(paths, MODULES):
        source = strip_comments(path.read_text(encoding='utf-8'))
        sources.append(source)
        if FORBIDDEN.search(source):
            raise ValueError('Forbidden proof escape in '+str(path))
        roots.extend(PREFIX+n for n in DECLARATION.findall(source))
        for dependency in imports(source):
            if dependency in all_modules and dependency not in seen:
                raise ValueError('Invalid dependency order: '+dependency)
        seen.add(PREFIX+name)
    if len(roots) != len(set(roots)) or not set(PROVED) <= set(roots):
        raise ValueError('Duplicate or missing declaration root')
    for target in set(TARGETS) - set(PROVED):
        pattern = re.compile(TARGET_DECLARATION.format(re.escape(target.removeprefix(PREFIX))))
        if target in roots or any(pattern.search(source) for source in sources):
            raise ValueError('Unregistered proof of a full target')
    return paths, set(roots)


# Compiler outputs that Lean loads for an imported module, as suffixes of `.olean`.
# Lake's `.hash` metadata is not a compiler output and is not bound.
NATIVE_COMPANIONS = ('', '.private', '.server')


def native_object(path: Path) -> Path:
    """The native `.olean` of a local source, relative to the Lean project."""
    return Path('.lake/build/lib/lean') / path.relative_to(LEAN).with_suffix('.olean')


def cached_artifact_hashes(paths: list[Path], rebuilt: list[Path]) -> dict[str, str]:
    """Bind every reused local dependency to its native compiler artifacts.

    A leftover temporary file from an interrupted write fails closed. Keys are
    sorted, so the record is independent of Python's hash seed.
    """
    cached = {}
    for path in sorted(set(paths) - set(rebuilt)):
        obj = LEAN / native_object(path)
        if not obj.is_file():
            raise ValueError('Missing cached dependency: ' + str(obj))
        for artifact in sorted(obj.parent.glob(obj.name + '*')):
            suffix = artifact.name[len(obj.name):]
            if '.tmp' in suffix:
                raise ValueError('Interrupted native artifact write: ' + str(artifact))
            if suffix in NATIVE_COMPANIONS:
                cached[artifact.relative_to(ROOT).as_posix()] = sha(artifact)
    return cached


def validate_stability(hashes: dict[str, str], audit: Path, audit_hash: str) -> None:
    if any(sha(ROOT/p) != h for p, h in hashes.items()) or sha(audit) != audit_hash:
        raise ValueError('Protected source or reused dependency artifact changed during audit')


def dependency_frontier(rebuilt: list[Path]) -> list[str]:
    """Local modules imported by the rebuilt modules but reused from earlier builds.

    Every reused local dependency is one of these or a transitive import of one.
    """
    rebuilt_paths = set(rebuilt)
    found = set()
    for path in rebuilt:
        for name in imports(strip_comments(path.read_text(encoding='utf-8'))):
            if name.startswith('ThresholdHC.') and module_path(name) not in rebuilt_paths:
                found.add(name)
    return sorted(found)


def dependency_command(lake: str, rebuilt: list[Path], build: bool) -> list[str] | None:
    """Ask Lake to confirm, or with build=True to bring, every reused dependency up to date.

    Lake compares current sources with its traces, so an artifact compiled from
    different or older sources is rejected (or rebuilt) instead of being trusted.
    """
    frontier = dependency_frontier(rebuilt)
    if not frontier:
        return None
    return [lake, 'build', *([] if build else ['--no-build']), *frontier]


def check_dependencies(lake: str, rebuilt: list[Path], output: Path, build: bool) -> dict | None:
    command = dependency_command(lake, rebuilt, build)
    if command is None:
        return None
    result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding='utf-8')
    text = result.stdout+result.stderr
    (output/'dependencies.log').write_text(text, encoding='utf-8')
    mode = 'build' if build else 'up-to-date check'
    print(f'reused dependencies, Lake {mode} of {len(dependency_frontier(rebuilt))} imported modules: '
          f'exit {result.returncode}', flush=True)
    if result.returncode:
        print(text, flush=True)
        print('Reused dependencies are missing or not up to date. Run the default Lake build '
              'first, or pass --build-dependencies.', flush=True)
    return dict(command=command, exit_code=result.returncode)


def native_commands(lake: str, rebuilt: list[Path]) -> list[list[str]]:
    """One single-threaded native compiler run per rebuilt module, in dependency order."""
    commands = []
    for path in rebuilt:
        obj = native_object(path)
        (LEAN/obj).parent.mkdir(parents=True, exist_ok=True)
        commands.append([lake, 'env', 'lean', '-j', '1', '-o', str(obj), str(path.relative_to(LEAN))])
    return commands


def write_audit_source(path: Path, source: str) -> None:
    """Write generated Lean with LF line endings, so its hash is platform independent."""
    path.write_bytes(source.encode('utf-8'))


def main() -> int:
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--cached-dependencies', action='store_true',
                        help='Rebuild registered modules natively and hash reused local artifacts')
    parser.add_argument('--build-dependencies', action='store_true',
                        help='With --cached-dependencies, let Lake build missing or stale reused '
                             'dependencies instead of only checking that they are up to date')
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--sequential', action='store_true')
    parser.add_argument('--require-complete', action='store_true')
    args = parser.parse_args()
    if args.build_dependencies and not args.cached_dependencies:
        parser.error('--build-dependencies requires --cached-dependencies')
    paths, roots = validate_sources()
    complete = set(PROVED) == set(TARGETS)
    if args.require_complete and not complete:
        print('Unproved full targets: '+', '.join(sorted(set(TARGETS)-set(PROVED))), flush=True)
        return 1
    ordered = dependency_order(paths)
    rebuilt = [p for p in ordered if p in paths]
    protected = set(ordered) | {
        Path(__file__).resolve(), ROOT/'tools/verify_blind_upper_components.py',
        ROOT/'tools/verify_entropy_tail_components.py',
        ROOT/'tools/verify_tier6.py', FREEZE,
        LEAN/'lean-toolchain', LEAN/'lake-manifest.json', LEAN/'lakefile.toml',
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT/'.runtime/entropy-tail'/datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True, exist_ok=False)
    targets = exact_targets()
    status = dict(valid=False, scope=SCOPE, source_sha256=hashes, full_targets=TARGETS,
                  exact_targets=targets, exact_targets_checked=0,
                  unproved_targets=sorted(set(TARGETS)-set(PROVED)),
                  entropy_tail_law_verified=False, commands=[],
                  cached_dependencies=args.cached_dependencies,
                  cached_dependency_artifact_sha256={}, dependency_check=None,
                  # Lake mode rebuilds only stale dependencies, so no full rebuild is claimed.
                  local_dependency_rebuild_performed=False,
                  build_mode='native_registered_modules' if args.cached_dependencies else 'lake_build')
    status_path = output/'status.json'

    def save():
        status_path.write_text(json.dumps(status, indent=2)+'\n', encoding='utf-8')
    save()
    cached = {}
    if args.cached_dependencies:
        status['dependency_check'] = check_dependencies(args.lake, rebuilt, output, args.build_dependencies)
        save()
        if status['dependency_check'] and status['dependency_check']['exit_code']:
            return status['dependency_check']['exit_code']
        cached = cached_artifact_hashes(ordered, rebuilt)
        status['cached_dependency_artifact_sha256'] = cached
        save()
    audit = LEAN/'.audit/EntropyTail.lean'
    audit.parent.mkdir(exist_ok=True)
    write_audit_source(audit, ''.join('import '+PREFIX+m+'\n' for m in MODULES)+'\n' +
                       ''.join(f'example : {t} := {d}\n' for d, t in targets.items())+'\n' +
                       ''.join('#print axioms '+r+'\n' for r in sorted(roots)))
    audit_hash = sha(audit)
    (output/'ExactAudit.lean').write_bytes(audit.read_bytes())
    status['audit_source_sha256'] = audit_hash
    save()
    modules = [PREFIX+name for name in MODULES]
    if args.cached_dependencies:
        commands = native_commands(args.lake, rebuilt)
    else:
        commands = ([[args.lake, 'build', m] for m in modules] if args.sequential
                    else [[args.lake, 'build', *modules]])
    commands.append([args.lake, 'env', 'lean', '-j', '1', str(audit.relative_to(LEAN))])
    for i, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding='utf-8')
        text = result.stdout+result.stderr
        (output/f'{i+1:02d}.log').write_text(text, encoding='utf-8')
        status['commands'].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f'{command[-1]}: exit {result.returncode}', flush=True)
        if result.returncode:
            print(text, flush=True)
            return result.returncode
    status['axioms'] = validate_reports(text, result.returncode, roots)
    validate_sources()
    validate_stability(hashes | cached, audit, audit_hash)
    status.update(valid=True, audited_modules=len(paths), audited_declarations=len(roots),
                  exact_targets_checked=len(targets), entropy_tail_law_verified=complete)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots),
                          targets_checked=len(targets), complete=complete,
                          evidence=str(output))), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
