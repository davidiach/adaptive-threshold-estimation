"""Check the full observable alpha > 2 rare-event theory.

Require all seven frozen full types, all project dependencies and every declaration axiom report.
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
SOURCE = LEAN / 'ThresholdHC/RareAboveTwo'
MODULES = ('BandModel', 'Model', 'PathBase', 'BandError', 'BudgetMath', 'ChargedPath', 'PathInformation', 'Specification', 'TerminalInformation', 'BandWork', 'Margin', 'MixtureInformation', 'Nonvacuity', 'PathVariation', 'PowerLaw', 'SignInformation', 'FiniteMixture', 'Parameters', 'Psi', 'WeightedMoment', 'KernelDistance', 'PathSign', 'PowerBounds', 'Terminal', 'PopulationError', 'SignMixture', 'StageWork', 'ConditionalWork', 'CoupledModel', 'SignDistance', 'Bias', 'Controller', 'GapKernel', 'PopulationWork', 'Execution', 'GapDistance', 'Increment', 'UniformWork', 'PopulationInformation', 'Unbiased', 'PrefixInformation', 'UnbiasedWork', 'Average', 'LowerSeparation', 'Realization', 'FixedModel', 'Lower', 'Single', 'FixedExecution', 'FixedIdentities', 'FixedBounds', 'Budget', 'Minimax', 'Full')
PREFIX = 'ThresholdHC.RareAboveTwo.'
FROZEN = {'lean/ThresholdHC/RareAboveTwo/Specification.lean': '53bab4bca5662f60659db55d83a497530dd39a974dde45b3514f394aa9482143'}
EXACT_TARGETS = {
    PREFIX+'power_law_exists': PREFIX+'PowerLawExistenceStatement',
    PREFIX+'rare_single_coin': PREFIX+'RareSingleCoinStatement',
    PREFIX+'rare_supported_lower': PREFIX+'RareSupportedLowerStatement',
    PREFIX+'above_two_upper': PREFIX+'AboveTwoUpperStatement',
    PREFIX+'above_two_minimax': PREFIX+'AboveTwoMinimaxStatement',
    PREFIX+'above_two_psi': PREFIX+'AboveTwoPsiStatement',
    PREFIX+'rare_nonvacuity': PREFIX+'RareNonvacuityStatement',
}
SCOPE = ('Full observable alpha > 2 rare-event theory: a law-independent single-coin construction, unbiased on every power-margin law, '
         'the matching supported-law lower bound, upper and exact-power minimax rates, Psi equivalence, '
         'law existence and nonvacuity. Budgets count actual flips and rarity is global.')


def validate_sources() -> tuple[list[Path], set[str]]:
    required_targets = {
        PREFIX+'power_law_exists': PREFIX+'PowerLawExistenceStatement',
        PREFIX+'rare_single_coin': PREFIX+'RareSingleCoinStatement',
        PREFIX+'rare_supported_lower': PREFIX+'RareSupportedLowerStatement',
        PREFIX+'above_two_upper': PREFIX+'AboveTwoUpperStatement',
        PREFIX+'above_two_minimax': PREFIX+'AboveTwoMinimaxStatement',
        PREFIX+'above_two_psi': PREFIX+'AboveTwoPsiStatement',
        PREFIX+'rare_nonvacuity': PREFIX+'RareNonvacuityStatement',
    }
    if EXACT_TARGETS != required_targets:
        raise ValueError('Missing or changed exact full target')
    freeze = json.loads((ROOT/'tools/rare_above_two_specification_freeze.json').read_text(encoding='utf-8'))
    if freeze['source_sha256'] != FROZEN or any(sha(ROOT/p) != h for p,h in FROZEN.items()):
        raise ValueError('Frozen rare-event specification changed')
    validate_dependency_freeze(SOURCE/'Specification.lean', freeze)
    paths = [module_path(PREFIX+m) for m in MODULES]
    if set(paths) != set(SOURCE.rglob('*.lean')):
        raise ValueError('Missing or unregistered rare-event module')
    # Imported project modules outside the registered package are hashed below,
    # but their sources must be free of proof escapes too.
    for path in sorted(project_dependencies(paths) - set(paths)):
        if FORBIDDEN.search(strip_comments(path.read_text(encoding='utf-8'))):
            raise ValueError('Forbidden proof escape in imported module '+str(path))
    roots, seen = [], set()
    all_modules = {PREFIX+m for m in MODULES}
    for path,name in zip(paths,MODULES):
        source = strip_comments(path.read_text(encoding='utf-8'))
        if FORBIDDEN.search(source):
            raise ValueError('Forbidden proof escape in '+str(path))
        roots.extend(PREFIX+n for n in DECLARATION.findall(source))
        for dependency in imports(source):
            if dependency in all_modules and dependency not in seen:
                raise ValueError('Invalid dependency order: '+dependency)
        seen.add(PREFIX+name)
    if len(roots) != len(set(roots)) or not set(EXACT_TARGETS) <= set(roots):
        raise ValueError('Duplicate or missing declaration root')
    return paths,set(roots)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--sequential',action='store_true')
    args = parser.parse_args()
    paths,roots = validate_sources()
    protected = project_dependencies(paths) | {
        Path(__file__).resolve(),ROOT/'tools/verify_blind_upper_components.py',
        ROOT/'tools/verify_tier6.py',ROOT/'tools/rare_above_two_specification_freeze.json',
        LEAN/'lean-toolchain',LEAN/'lake-manifest.json',LEAN/'lakefile.toml',
    }
    hashes = {p.relative_to(ROOT).as_posix():sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT/'.runtime/rare-above-two'/datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True,exist_ok=False)
    status = dict(valid=False,scope=SCOPE,source_sha256=hashes,exact_targets=EXACT_TARGETS,
                  exact_targets_checked=0,rare_above_two_verified=False,commands=[])
    status_path = output/'status.json'
    def save():
        status_path.write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
    save()
    audit = LEAN/'.audit/RareAboveTwo.lean'
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(''.join('import '+PREFIX+m+'\n' for m in MODULES)+'\n'+
                    ''.join(f'example : {t} := {d}\n' for d,t in EXACT_TARGETS.items())+'\n'+
                    ''.join('#print axioms '+r+'\n' for r in sorted(roots)),encoding='utf-8')
    modules=[PREFIX+name for name in MODULES]
    commands=[['lake','build',m] for m in modules] if args.sequential else [['lake','build',*modules]]
    commands.append(['lake','env','lean',str(audit.relative_to(LEAN))])
    for i,command in enumerate(commands):
        result=subprocess.run(command,cwd=LEAN,capture_output=True,text=True,encoding='utf-8')
        text=result.stdout+result.stderr
        (output/f'{i+1:02d}.log').write_text(text,encoding='utf-8')
        status['commands'].append(dict(command=command,exit_code=result.returncode))
        save()
        print(f'{command[-1]}: exit {result.returncode}',flush=True)
        if result.returncode:
            print(text,flush=True)
            return result.returncode
    status['axioms']=validate_reports(text,result.returncode,roots)
    validate_sources()
    if any(sha(ROOT/p)!=h for p,h in hashes.items()):
        raise ValueError('Protected source changed during audit')
    status.update(valid=True,audited_modules=len(paths),audited_declarations=len(roots),
                  exact_targets_checked=len(EXACT_TARGETS),rare_above_two_verified=True)
    save()
    print(json.dumps(dict(valid=True,modules=len(paths),declarations=len(roots),evidence=str(output))),flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
