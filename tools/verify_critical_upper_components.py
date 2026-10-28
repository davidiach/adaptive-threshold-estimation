"""Kernel-check the full critical upper theorem and its observable construction.

Run after the existing critical and distribution-blind builds. Every declaration
in CriticalUpper is kernel checked and audited for transitive axioms. The final
statements remain byte-identical to their pre-proof freeze. Both full targets
must be inhabited without additional hypotheses before completion is certified.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, IMPORT, module_path, project_dependencies, sha,
    strip_comments, validate_reports,
)

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
SOURCE = LEAN / 'ThresholdHC/CriticalUpper'
MODULES = ('Specification', 'GapIntegration', 'CappedCost', 'WeightedCost',
           'ScreenModel', 'ScreenError', 'ScreenWork', 'ScreenCoin',
           'ScreenPopulation', 'ScreenMoments', 'Parameters', 'Calibration',
           'CoupledModel', 'CoinLaw', 'Increment', 'Unbiased', 'UnbiasedWork',
           'UnbiasedPopulation', 'Average', 'Simulation', 'FixedModel',
           'FixedExecution', 'FixedIdentities', 'FixedBounds', 'Budget', 'Full')
PREFIX = 'ThresholdHC.CriticalUpper.'
SPECIFICATION_SHA256 = '2e6482ac338da26b5ceaf4bfac38cf63bff401aa934e43ea19f21368625a21ae'
EXACT_TARGETS = {
    PREFIX+'critical_upper_bound': PREFIX+'CriticalUpperStatement',
    PREFIX+'critical_minimax_upper_bound': PREFIX+'CriticalMinimaxUpperStatement',
}
SCOPE = ('Full critical algorithmic and minimax upper bounds with universal '
         'coefficient 100000, for every allowed rarity and budget in the '
         'original observable experiment. Includes asymmetric classifiers, '
         'exact quadratic-law '
         'integration, population error/work bounds under global rarity, and '
         'parameter calibration, observable random-level estimation, exact '
         'population unbiasedness, extended second moment at most 28*rho, and '
         'actual expected work at most 112000000*criticalLogFactor(rho). '
         'Independent call arrays, the measurable fixed-count controller, exact '
         'population execution and work/output identities, budget selection '
         'and saturation are proved. The explicit Psi comparison is not certified.')


def validate_exact_targets(targets: dict[str, str]) -> None:
    required = {
        PREFIX+'critical_upper_bound': PREFIX+'CriticalUpperStatement',
        PREFIX+'critical_minimax_upper_bound': PREFIX+'CriticalMinimaxUpperStatement',
    }
    if targets != required:
        raise ValueError('Missing or changed frozen full-theorem target')


def validate_sources() -> tuple[list[Path], set[str]]:
    validate_exact_targets(EXACT_TARGETS)
    paths = [module_path(PREFIX + name) for name in MODULES]
    if set(paths) != set(SOURCE.glob('*.lean')):
        raise ValueError('Missing or unregistered critical-upper source')
    if sha(SOURCE / 'Specification.lean') != SPECIFICATION_SHA256:
        raise ValueError('Frozen critical-upper specification changed')
    freeze = json.loads((ROOT / 'tools/critical_upper_specification_freeze.json').read_text())
    if freeze['sha256'] != SPECIFICATION_SHA256 or freeze['path'] != 'lean/ThresholdHC/CriticalUpper/Specification.lean':
        raise ValueError('Frozen specification registration changed')
    roots = []
    seen = set()
    all_modules = {PREFIX + name for name in MODULES}
    for path, name in zip(paths, MODULES):
        text = strip_comments(path.read_text(encoding='utf-8'))
        if FORBIDDEN.search(text):
            raise ValueError('Forbidden proof escape in ' + str(path))
        roots.extend(PREFIX + name for name in DECLARATION.findall(text))
        for dependency in IMPORT.findall(text):
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
        'criticalUnbiased_population_second_moment', 'criticalUnbiased_population_work',
        'critical_observable_simulation_law', 'FixedConsumes.path_eq',
        'fixed_population_output', 'fixed_population_work', 'fixed_squaredRisk_bound',
        'fixed_expectedWork_bound', 'criticalBudget_uniformBudget',
        'criticalBudget_maximalRMSRisk', 'critical_upper_bound', 'critical_minimax_upper_bound')}
    if not required <= set(roots):
        raise ValueError('Missing component target')
    return paths, set(roots)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    paths, roots = validate_sources()
    protected = project_dependencies(paths) | {
        Path(__file__).resolve(), ROOT / 'tools/verify_blind_upper_components.py',
        ROOT / 'tools/verify_tier6.py', ROOT / 'tools/critical_upper_specification_freeze.json',
        LEAN / 'lean-toolchain', LEAN / 'lake-manifest.json',
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / '.runtime/critical-upper-components' / datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True, exist_ok=False)
    status = dict(valid=False, scope=SCOPE, full_critical_upper_verified=False,
                  full_critical_minimax_upper_verified=False, explicit_psi_comparison_verified=False,
                  exact_targets=EXACT_TARGETS, exact_targets_checked=0,
                  specification_sha256=SPECIFICATION_SHA256, source_sha256=hashes, commands=[])
    status_path = output / 'status.json'
    def save():
        status_path.write_text(json.dumps(status, indent=2)+'\n', encoding='utf-8')
    save()
    audit = LEAN / '.audit/CriticalUpperComponents.lean'
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(''.join('import '+PREFIX+m+'\n' for m in MODULES)+'\n'+
                     ''.join(f'example : {target} := {declaration}\n'
                             for declaration, target in EXACT_TARGETS.items())+'\n'+
                     ''.join('#print axioms '+r+'\n' for r in sorted(roots)), encoding='utf-8')
    commands = []
    for path, name in zip(paths, MODULES):
        target = LEAN / '.lake/build/lib/lean/ThresholdHC/CriticalUpper' / (name+'.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        commands.append(['lake', 'env', 'lean', '-o', str(target), str(path.relative_to(LEAN))])
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
    status.update(valid=True, audited_modules=len(paths), audited_declarations=len(roots),
                  exact_targets_checked=len(EXACT_TARGETS), full_critical_upper_verified=True,
                  full_critical_minimax_upper_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots),
                          full_critical_upper_verified=True, evidence=str(output))), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
