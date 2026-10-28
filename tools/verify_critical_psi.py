"""Check the actual critical-law Psi formula, rate and minimax counterexample.

Lake rebuilds stale prerequisites before the kernel and axiom checks. The full
statements, variational model and their local dependencies must match the recorded
hashes. This does not certify an arbitrary-law replacement. Use --sequential to
build one registered module at a time on constrained machines.
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
SOURCE = LEAN / 'ThresholdHC/CriticalPsi'
MODULES = ('Model', 'Specification', 'Formula', 'Rate', 'Separation', 'Full')
PREFIX = 'ThresholdHC.CriticalPsi.'
FROZEN = {
    'lean/ThresholdHC/CriticalPsi/Model.lean':
        'b660247a37ebb62cd94315cd932c4819d759767f764272ee6e6fdd41dec86f1f',
    'lean/ThresholdHC/CriticalPsi/Specification.lean':
        '348a5e59928bfe6162b3882a6513293b6fea2bfa68dee462d9b5a159eaf1c911',
}
EXACT_TARGETS = {
    PREFIX+'critical_psi_formula': PREFIX+'CriticalPsiFormulaStatement',
    PREFIX+'critical_psi_rate': PREFIX+'CriticalPsiRateStatement',
    PREFIX+'critical_matching_psi_refuted': PREFIX+'CriticalPsiSeparationStatement',
}
SCOPE = ('Exact critical-law variational supremum over all measurable feasible '
         'allocations: attained cutoff formula, two-sided rate with constants 1 '
         'and 16, and no universal finite matching-Psi upper for the original '
         'unrestricted critical minimax risk. The separation uses rarity '
         'exp(-exp(M)) and budget L*(1+log(L))/rho. It does not assert a new '
         'arbitrary-law characterization or formalize the paper\'s particular '
         'budget sequence rho^(-2).')


def validate_sources() -> tuple[list[Path], set[str]]:
    required_targets = {
        PREFIX+'critical_psi_formula': PREFIX+'CriticalPsiFormulaStatement',
        PREFIX+'critical_psi_rate': PREFIX+'CriticalPsiRateStatement',
        PREFIX+'critical_matching_psi_refuted': PREFIX+'CriticalPsiSeparationStatement',
    }
    if EXACT_TARGETS != required_targets:
        raise ValueError('Missing or changed exact full target')
    freeze = json.loads((ROOT/'tools/critical_psi_specification_freeze.json').read_text(encoding='utf-8'))
    if freeze['source_sha256'] != FROZEN or any(sha(ROOT/p) != h for p,h in FROZEN.items()):
        raise ValueError('Frozen variational model or specification changed')
    validate_dependency_freeze(SOURCE/'Specification.lean', freeze)
    paths = [module_path(PREFIX+m) for m in MODULES]
    if set(paths) != set(SOURCE.glob('*.lean')):
        raise ValueError('Missing or unregistered Psi module')
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
        ROOT/'tools/verify_tier6.py',ROOT/'tools/critical_psi_specification_freeze.json',
        LEAN/'lean-toolchain',LEAN/'lake-manifest.json',LEAN/'lakefile.toml',
    }
    hashes = {p.relative_to(ROOT).as_posix():sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT/'.runtime/critical-psi'/datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True,exist_ok=False)
    status = dict(valid=False,scope=SCOPE,source_sha256=hashes,exact_targets=EXACT_TARGETS,
                  exact_targets_checked=0,critical_psi_formula_verified=False,
                  critical_psi_rate_verified=False,critical_matching_psi_refuted=False,commands=[])
    status_path = output/'status.json'
    def save():
        status_path.write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
    save()
    audit = LEAN/'.audit/CriticalPsi.lean'
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
                  exact_targets_checked=len(EXACT_TARGETS),critical_psi_formula_verified=True,
                  critical_psi_rate_verified=True,critical_matching_psi_refuted=True)
    save()
    print(json.dumps(dict(valid=True,modules=len(paths),declarations=len(roots),evidence=str(output))),flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
