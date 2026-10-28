"""Check critical-upper estimator components; the full upper theorem is pending.

Lake rebuilds any stale prerequisite, so earlier critical and distribution-blind
runs only save time. Every declaration in CriticalUpper is kernel checked and
audited for transitive axioms. The final statement remains byte-identical to its
pre-proof freeze, and every project source it imports matches its recorded hash;
it is not yet inhabited. Use --sequential on memory-limited runners.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, IMPORT, module_path, project_dependencies, sha,
    strip_comments, validate_reports, imports, validate_dependency_freeze,
)

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
SOURCE = LEAN / 'ThresholdHC/CriticalUpper'
MODULES = ('Specification', 'GapIntegration', 'CappedCost', 'WeightedCost',
           'ScreenModel', 'ScreenError', 'ScreenWork', 'ScreenCoin',
           'ScreenPopulation', 'ScreenMoments', 'Parameters', 'Calibration',
           'CoupledModel', 'CoinLaw', 'Increment', 'Unbiased', 'UnbiasedWork',
           'UnbiasedPopulation')
PREFIX = 'ThresholdHC.CriticalUpper.'
SPECIFICATION_SHA256 = '2e6482ac338da26b5ceaf4bfac38cf63bff401aa934e43ea19f21368625a21ae'
FREEZE = ROOT / 'tools/critical_upper_specification_freeze.json'
SCOPE = ('Observable asymmetric single-coin classifiers, exact quadratic-law '
         'integration, population error/work bounds under global rarity, and '
         'parameter calibration, observable random-level estimation, exact '
         'population unbiasedness, extended second moment at most 28*rho, and '
         'actual expected work at most 112000000*criticalLogFactor(rho). '
         'Budgeted fresh-coin aggregation, its Tier 6 realization, and the '
         'full critical upper theorem are not certified.')


def validate_sources() -> tuple[list[Path], set[str]]:
    paths = [module_path(PREFIX + name) for name in MODULES]
    if set(paths) != set(SOURCE.glob('*.lean')):
        raise ValueError('Missing or unregistered critical-upper source')
    if sha(SOURCE / 'Specification.lean') != SPECIFICATION_SHA256:
        raise ValueError('Frozen critical-upper specification changed')
    freeze = json.loads(FREEZE.read_text(encoding='utf-8'))
    if freeze['sha256'] != SPECIFICATION_SHA256 or freeze['path'] != 'lean/ThresholdHC/CriticalUpper/Specification.lean':
        raise ValueError('Frozen specification registration changed')
    # The statement's meaning lives in the definitions it imports; freeze those too.
    validate_dependency_freeze(SOURCE / 'Specification.lean', freeze)
    roots = []
    seen = set()
    all_modules = {PREFIX + name for name in MODULES}
    for path, name in zip(paths, MODULES):
        text = strip_comments(path.read_text(encoding='utf-8'))
        if FORBIDDEN.search(text):
            raise ValueError('Forbidden proof escape in ' + str(path))
        roots.extend(PREFIX + name for name in DECLARATION.findall(text))
        for dependency in imports(text):
            if dependency in all_modules and dependency not in seen:
                raise ValueError('Invalid component dependency order: ' + dependency)
        seen.add(PREFIX + name)
    if len(roots) != len(set(roots)):
        raise ValueError('Duplicate audit declaration')
    required = {PREFIX + name for name in (
        'CriticalUpperStatement', 'CriticalMinimaxUpperStatement',
        'criticalCappedCost_weighted_le', 'screen_coin_error', 'screen_coin_work',
        'screen_population_error_le', 'screen_population_work_le',
        'screen_population_bias_le', 'screen_population_second_moment_le',
        'calibratedScreen_error', 'calibratedScreen_work',
        'criticalUnbiased_population_integrable', 'criticalUnbiased_population_mean',
        'criticalUnbiased_population_second_moment', 'criticalUnbiased_population_work')}
    if not required <= set(roots):
        raise ValueError('Missing component target')
    return paths, set(roots)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--sequential', action='store_true')
    args = parser.parse_args()
    paths, roots = validate_sources()
    protected = project_dependencies(paths) | {
        Path(__file__).resolve(), ROOT / 'tools/verify_blind_upper_components.py',
        ROOT / 'tools/verify_tier6.py', FREEZE,
        LEAN / 'lean-toolchain', LEAN / 'lake-manifest.json', LEAN / 'lakefile.toml',
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / '.runtime/critical-upper-components' / datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True, exist_ok=False)
    status = dict(valid=False, scope=SCOPE, full_critical_upper_verified=False,
                  specification_sha256=SPECIFICATION_SHA256, source_sha256=hashes, commands=[])
    status_path = output / 'status.json'
    def save():
        status_path.write_text(json.dumps(status, indent=2)+'\n', encoding='utf-8')
    save()
    audit = LEAN / '.audit/CriticalUpperComponents.lean'
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(''.join('import '+PREFIX+m+'\n' for m in MODULES)+'\n'+
                     ''.join('#print axioms '+r+'\n' for r in sorted(roots)), encoding='utf-8')
    modules = [PREFIX+name for name in MODULES]
    commands = [['lake', 'build', m] for m in modules] if args.sequential else [['lake', 'build', *modules]]
    commands.append(['lake', 'env', 'lean', str(audit.relative_to(LEAN))])
    for i, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding='utf-8')
        text = result.stdout + result.stderr
        (output / f'{i+1:02d}.log').write_text(text, encoding='utf-8')
        status['commands'].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f'{command[-1]}: exit {result.returncode}', flush=True)
        if result.returncode:
            print(text, flush=True)
            return result.returncode
    status['axioms'] = validate_reports(text, result.returncode, roots)
    validate_sources()
    if any(sha(ROOT / rel) != digest for rel, digest in hashes.items()):
        raise ValueError('Protected source changed during audit')
    status.update(valid=True, audited_modules=len(paths), audited_declarations=len(roots))
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots),
                          full_critical_upper_verified=False, evidence=str(output))), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
