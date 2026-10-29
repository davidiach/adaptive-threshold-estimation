"""Check the canonical revealed- and selected-magnitude oracle lower bounds.

Require all eight frozen full types, all project dependencies and every declaration axiom report.
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
SOURCE = LEAN / 'ThresholdHC/OracleLower'
MODULES = ('Model', 'Specification', 'Realization', 'SelectedSemantics', 'Information', 'RMS', 'Confidence', 'Nonvacuity', 'Examples', 'Full')
PREFIX = 'ThresholdHC.OracleLower.'
FROZEN = {'lean/ThresholdHC/OracleLower/Specification.lean': 'a58e3e76ae57b299956c76a7f156bfa958f9d86f16908b175dcbec4596b65136'}
EXACT_TARGETS = {
    PREFIX+'oracle_realization': PREFIX+'OracleRealizationStatement',
    PREFIX+'selected_semantics': PREFIX+'SelectedSemanticsStatement',
    PREFIX+'oracle_rms_lower': PREFIX+'OracleRMSLowerStatement',
    PREFIX+'oracle_confidence_lower': PREFIX+'OracleConfidenceLowerStatement',
    PREFIX+'revealed_lower_bounds': PREFIX+'RevealedLowerStatement',
    PREFIX+'selected_lower_bounds': PREFIX+'SelectedLowerStatement',
    PREFIX+'oracle_minimax_lower': PREFIX+'OracleMinimaxLowerStatement',
    PREFIX+'oracle_nonvacuity': PREFIX+'OracleNonvacuityStatement',
}
SCOPE = ('RMS lower coefficient 1/64 and confidence lower coefficient 15/(256 sqrt 2) '
         'for canonical revealed and adaptively selected magnitude experiments. '
         'Includes actual expected-flip budgets, arbitrary measurable seeds, '
         'fresh/revisit semantics, minimax statements and nonvacuity.')


def validate_sources() -> tuple[list[Path], set[str]]:
    required_targets = {
        PREFIX+'oracle_realization': PREFIX+'OracleRealizationStatement',
        PREFIX+'selected_semantics': PREFIX+'SelectedSemanticsStatement',
        PREFIX+'oracle_rms_lower': PREFIX+'OracleRMSLowerStatement',
        PREFIX+'oracle_confidence_lower': PREFIX+'OracleConfidenceLowerStatement',
        PREFIX+'revealed_lower_bounds': PREFIX+'RevealedLowerStatement',
        PREFIX+'selected_lower_bounds': PREFIX+'SelectedLowerStatement',
        PREFIX+'oracle_minimax_lower': PREFIX+'OracleMinimaxLowerStatement',
        PREFIX+'oracle_nonvacuity': PREFIX+'OracleNonvacuityStatement',
    }
    if EXACT_TARGETS != required_targets:
        raise ValueError('Missing or changed exact full target')
    freeze = json.loads((ROOT/'tools/oracle_lower_specification_freeze.json').read_text(encoding='utf-8'))
    if freeze['source_sha256'] != FROZEN or any(sha(ROOT/p) != h for p,h in FROZEN.items()):
        raise ValueError('Frozen oracle specification changed')
    validate_dependency_freeze(SOURCE/'Specification.lean', freeze)
    paths = [module_path(PREFIX+m) for m in MODULES]
    if set(paths) != set(SOURCE.glob('*.lean')):
        raise ValueError('Missing or unregistered oracle module')
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
        ROOT/'tools/verify_tier6.py',ROOT/'tools/oracle_lower_specification_freeze.json',
        LEAN/'lean-toolchain',LEAN/'lake-manifest.json',LEAN/'lakefile.toml',
    }
    hashes = {p.relative_to(ROOT).as_posix():sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT/'.runtime/oracle-lower'/datetime.now(
        timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True,exist_ok=False)
    status = dict(valid=False,scope=SCOPE,source_sha256=hashes,exact_targets=EXACT_TARGETS,
                  exact_targets_checked=0,oracle_lower_verified=False,commands=[])
    status_path = output/'status.json'
    def save():
        status_path.write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
    save()
    audit = LEAN/'.audit/OracleLower.lean'
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
                  exact_targets_checked=len(EXACT_TARGETS),oracle_lower_verified=True)
    save()
    print(json.dumps(dict(valid=True,modules=len(paths),declarations=len(roots),evidence=str(output))),flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
