"""Check the quantile-comparison formalization against its frozen target type.

The frozen specification fixes one full target: the scalar inequality of
Lemma 3 in the certified-selection research package. A registered target is
checked for its exact type and transitive axioms. Use --require-complete to
fail while the target is unproved. The comparison K <= Q <= (8/5)K itself and
Lemmas 1-2 are not targets.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, module_path, project_dependencies, sha,
    strip_comments, validate_reports, imports, validate_dependency_freeze,
)

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
SOURCE = LEAN / 'ThresholdHC/QuantileComparison'
FREEZE = ROOT / 'tools/quantile_comparison_specification_freeze.json'
MODULES = ('Specification', 'Scalar')
PREFIX = 'ThresholdHC.QuantileComparison.'
FROZEN = {'lean/ThresholdHC/QuantileComparison/Specification.lean':
          '434b95f79d8464596cf52c34bbbdda9c90f65b274d55874c5f4ab404bd88a6b2'}
TARGETS = {PREFIX+'scalar_comparison': PREFIX+'ScalarComparisonStatement'}
# Targets whose proofs are present. A target is proved only by its registered name.
PROVED: tuple[str, ...] = (PREFIX+'scalar_comparison',)
# Any declaration form of a target name, including modifiers such as `protected` and
# fully qualified names, which the shared root pattern does not report.
TARGET_DECLARATION = (r"\b(?:def|abbrev|structure|theorem|lemma|instance|inductive)\s+"
                      r"(?:_root_\.)?(?:" + re.escape(PREFIX) + r")?{}(?![\w'.])")
SCOPE = ('Scalar inequality of Lemma 3 in the certified-selection research package: '
         'T + sqrt(v^2 + 2Tc + 2v sqrt(Tc)) <= (8/5)(sqrt(T^2 + v^2) + c) for all real '
         'T, v, c >= 0. The comparison K <= Q <= (8/5)K and Lemmas 1-2 are not targets.')


def exact_targets() -> dict[str, str]:
    return {name: TARGETS[name] for name in PROVED}


def validate_sources() -> tuple[list[Path], set[str]]:
    required_targets = {PREFIX+'scalar_comparison': PREFIX+'ScalarComparisonStatement'}
    if TARGETS != required_targets:
        raise ValueError('Missing or changed exact full target')
    if len(PROVED) != len(set(PROVED)) or not set(PROVED) <= set(TARGETS):
        raise ValueError('Unknown or duplicate proved target')
    freeze = json.loads(FREEZE.read_text(encoding='utf-8'))
    if freeze['source_sha256'] != FROZEN or any(sha(ROOT/p) != h for p, h in FROZEN.items()):
        raise ValueError('Frozen quantile-comparison specification changed')
    if freeze['targets'] != TARGETS:
        raise ValueError('Missing or changed exact full target')
    validate_dependency_freeze(SOURCE/'Specification.lean', freeze)
    paths = [module_path(PREFIX+m) for m in MODULES]
    if set(paths) != set(SOURCE.rglob('*.lean')):
        raise ValueError('Missing or unregistered quantile-comparison module')
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
    output = args.output_dir or ROOT/'.runtime/quantile-comparison'/datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True, exist_ok=False)
    targets = exact_targets()
    status = dict(valid=False, scope=SCOPE, source_sha256=hashes, full_targets=TARGETS,
                  exact_targets=targets, exact_targets_checked=0,
                  unproved_targets=sorted(set(TARGETS)-set(PROVED)),
                  scalar_comparison_verified=False, commands=[])
    status_path = output/'status.json'

    def save():
        status_path.write_text(json.dumps(status, indent=2)+'\n', encoding='utf-8')
    save()
    audit = LEAN/'.audit/QuantileComparison.lean'
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
                  exact_targets_checked=len(targets), scalar_comparison_verified=complete)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots),
                          targets_checked=len(targets), complete=complete,
                          evidence=str(output))), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
