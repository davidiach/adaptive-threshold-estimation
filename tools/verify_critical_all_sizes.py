"""Audit all-size finite-gap entropy and explicit single-coin base costs.

This checks four complete target types and every declaration in the extension.
The locked target/dependency snapshot was made during implementation. It is
not a claim of independent specification or before-proof freezing.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, project_dependencies, sha, strip_comments,
    validate_reports, imports, validate_dependency_freeze,
)

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
SOURCE = LEAN / 'ThresholdHC/CriticalAllSizes'
PREFIX = 'ThresholdHC.CriticalAllSizes.'
SPECIFICATION_SHA256 = '8c908af5b0008ac17d9f87ea0b3228b6d4b24f0eaa4b68ffad8f68be14a1f17e'
MODULES = ('Specification', 'SingleGap', 'FiniteGap', 'Estimation', 'Scale',
           'Product', 'Asymptotics', 'BaseCost')
TARGET_NAMES = {
    'finite_gap_sign_entropy_all': 'AllGapStatement',
    'finite_gap_estimation_entropy_all': 'AllGapEstimationStatement',
    'critical_raw_base_cost_explicit': 'ExplicitRawBaseCostStatement',
    'critical_base_cost_explicit': 'ExplicitBaseCostStatement',
}
EXACT_TARGETS = {PREFIX+k: PREFIX+v for k,v in TARGET_NAMES.items()}
SCOPE = ('Finite-gap sign entropy for all natural gap counts with coefficient '
         '1/4096; estimator and population-scale consequences; raw second '
         'moment times null work at least rho*L*H/10000000000 and variance '
         'times null work at least rho*L*H/15000000000 for actual observable '
         'single-coin procedures. The original 1/512 large-count bound remains '
         'unchanged. No new explicit population minimax constant is asserted.')


def validate_sources():
    required = {
        PREFIX+'finite_gap_sign_entropy_all': PREFIX+'AllGapStatement',
        PREFIX+'finite_gap_estimation_entropy_all': PREFIX+'AllGapEstimationStatement',
        PREFIX+'critical_raw_base_cost_explicit': PREFIX+'ExplicitRawBaseCostStatement',
        PREFIX+'critical_base_cost_explicit': PREFIX+'ExplicitBaseCostStatement',
    }
    if EXACT_TARGETS != required:
        raise ValueError('Missing or changed exact target')
    lock = json.loads((ROOT/'tools/critical_all_sizes_specification_lock.json').read_text(encoding='utf-8'))
    spec = SOURCE/'Specification.lean'
    if (lock['source'] != spec.relative_to(ROOT).as_posix()
            or lock['sha256'] != SPECIFICATION_SHA256 or sha(spec) != SPECIFICATION_SHA256):
        raise ValueError('Locked specification changed')
    validate_dependency_freeze(spec, lock)
    paths = [SOURCE/(m+'.lean') for m in MODULES]
    if set(paths) != set(SOURCE.glob('*.lean')):
        raise ValueError('Missing or unregistered extension module')
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--sequential',action='store_true')
    args = parser.parse_args()
    paths,roots = validate_sources()
    protected = project_dependencies(paths) | {
        Path(__file__).resolve(), ROOT/'tools/verify_blind_upper_components.py',
        ROOT/'tools/verify_tier6.py', ROOT/'tools/critical_all_sizes_specification_lock.json',
        LEAN/'lean-toolchain', LEAN/'lake-manifest.json', LEAN/'lakefile.toml',
    }
    hashes = {p.relative_to(ROOT).as_posix():sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT/'.runtime/critical-all-sizes'/datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True,exist_ok=False)
    status = dict(valid=False,scope=SCOPE,source_sha256=hashes,exact_targets=EXACT_TARGETS,
                  exact_targets_checked=0,specifications_frozen_before_proofs=False,commands=[])
    def save():
        (output/'status.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
    save()
    audit = LEAN/'.audit/CriticalAllSizes.lean'
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(''.join('import '+PREFIX+m+'\n' for m in MODULES)+'\n'+
                    ''.join(f'example : {t} := {d}\n' for d,t in EXACT_TARGETS.items())+'\n'+
                    ''.join('#print axioms '+r+'\n' for r in sorted(roots)),encoding='utf-8')
    modules = [PREFIX+m for m in MODULES]
    commands = [['lake','build',m] for m in modules] if args.sequential else [['lake','build',*modules]]
    commands.append(['lake','env','lean',str(audit.relative_to(LEAN))])
    for i,command in enumerate(commands):
        result = subprocess.run(command,cwd=LEAN,capture_output=True,text=True,encoding='utf-8')
        text = result.stdout+result.stderr
        (output/f'{i+1:02d}.log').write_text(text,encoding='utf-8')
        status['commands'].append(dict(command=command,exit_code=result.returncode))
        save()
        print(f'{command[-1]}: exit {result.returncode}',flush=True)
        if result.returncode:
            print(text,flush=True)
            return result.returncode
    status['axioms'] = validate_reports(text,result.returncode,roots)
    validate_sources()
    if any(sha(ROOT/p) != h for p,h in hashes.items()):
        raise ValueError('Protected source changed during audit')
    status.update(valid=True,audited_modules=len(paths),audited_declarations=len(roots),
                  exact_targets_checked=len(EXACT_TARGETS))
    save()
    print(json.dumps(dict(valid=True,modules=len(paths),declarations=len(roots),evidence=str(output))))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
