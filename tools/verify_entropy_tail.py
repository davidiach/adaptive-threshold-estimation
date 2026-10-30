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
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, module_path, project_dependencies, sha,
    strip_comments, validate_reports, imports, validate_dependency_freeze,
)

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
SOURCE = LEAN / 'ThresholdHC/EntropyTail'
FREEZE = ROOT / 'tools/entropy_tail_specification_freeze.json'
MODULES = ('Model', 'Specification')
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
PROVED = ()
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
    roots, seen = [], set()
    all_modules = {PREFIX+m for m in MODULES}
    for path, name in zip(paths, MODULES):
        source = strip_comments(path.read_text(encoding='utf-8'))
        if FORBIDDEN.search(source):
            raise ValueError('Forbidden proof escape in '+str(path))
        roots.extend(PREFIX+n for n in DECLARATION.findall(source))
        for dependency in imports(source):
            if dependency in all_modules and dependency not in seen:
                raise ValueError('Invalid dependency order: '+dependency)
        seen.add(PREFIX+name)
    if len(roots) != len(set(roots)) or not set(PROVED) <= set(roots):
        raise ValueError('Duplicate or missing declaration root')
    if (set(TARGETS) - set(PROVED)) & set(roots):
        raise ValueError('Unregistered proof of a full target')
    return paths, set(roots)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--sequential', action='store_true')
    parser.add_argument('--require-complete', action='store_true')
    args = parser.parse_args()
    paths, roots = validate_sources()
    complete = set(PROVED) == set(TARGETS)
    if args.require_complete and not complete:
        print('Unproved full targets: '+', '.join(sorted(set(TARGETS)-set(PROVED))), flush=True)
        return 1
    protected = project_dependencies(paths) | {
        Path(__file__).resolve(), ROOT/'tools/verify_blind_upper_components.py',
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
                  entropy_tail_law_verified=False, commands=[])
    status_path = output/'status.json'

    def save():
        status_path.write_text(json.dumps(status, indent=2)+'\n', encoding='utf-8')
    save()
    audit = LEAN/'.audit/EntropyTail.lean'
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(''.join('import '+PREFIX+m+'\n' for m in MODULES)+'\n' +
                     ''.join(f'example : {t} := {d}\n' for d, t in targets.items())+'\n' +
                     ''.join('#print axioms '+r+'\n' for r in sorted(roots)), encoding='utf-8')
    modules = [PREFIX+name for name in MODULES]
    commands = [['lake', 'build', m] for m in modules] if args.sequential else [['lake', 'build', *modules]]
    commands.append(['lake', 'env', 'lean', str(audit.relative_to(LEAN))])
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
    if any(sha(ROOT/p) != h for p, h in hashes.items()):
        raise ValueError('Protected source changed during audit')
    status.update(valid=True, audited_modules=len(paths), audited_declarations=len(roots),
                  exact_targets_checked=len(targets), entropy_tail_law_verified=complete)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots),
                          targets_checked=len(targets), complete=complete,
                          evidence=str(output))), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
