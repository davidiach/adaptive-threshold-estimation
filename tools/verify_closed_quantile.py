"""Audit the universal closed-quantile minimax corollary in the original model.

Default: rebuild the complete local dependency closure. Cached mode rebuilds
the two registered modules and binds reused native artifacts to the run.
The explicit paper lower coefficient and direct finite-law proof are not targets.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, module_path, sha, strip_comments,
    validate_dependency_freeze, validate_reports,
)
from verify_entropy_tail_components import dependency_order
from verify_entropy_tail import cached_artifact_hashes, validate_stability

ROOT=Path(__file__).resolve().parents[1]
LEAN=ROOT/'lean'
SOURCE=LEAN/'ThresholdHC/ClosedQuantile'
PREFIX='ThresholdHC.ClosedQuantile.'
MODULES=('Specification','Full')
FREEZE=ROOT/'tools/closed_quantile_specification_freeze.json'
FROZEN={'lean/ThresholdHC/ClosedQuantile/Specification.lean': 'fa38d28d8fd59a89703e21b10b67a67efd59c56aa33d68eba86f2985283d66f6'}
EXACT_TARGETS={PREFIX+'closed_quantile_law': PREFIX+'ClosedQuantileLawStatement'}
SCOPE=('Universal two-sided comparison of the original observable minimax RMS risk '
       'and the fractional-boundary closed quantile functional for every probability '
       'law on (0,1/2], 0 < rho <= 1/4 and B > 0. Actual expected flips, global rarity, '
       'hidden magnitudes/signs. Conservative universal constants; no claim to the '
       'paper explicit lower coefficient or its direct finite-law proof.')


def validate_sources() -> tuple[list[Path], list[Path], set[str]]:
    required={PREFIX+'closed_quantile_law': PREFIX+'ClosedQuantileLawStatement'}
    if EXACT_TARGETS != required:
        raise ValueError('Missing or changed exact closed-quantile target')
    freeze=json.loads(FREEZE.read_text(encoding='utf-8'))
    if freeze.get('source_sha256') != FROZEN or any(sha(ROOT/p)!=h for p,h in FROZEN.items()):
        raise ValueError('Frozen closed-quantile specification changed')
    if freeze.get('targets') != required:
        raise ValueError('Missing or changed exact closed-quantile target')
    validate_dependency_freeze(SOURCE/'Specification.lean',freeze)
    paths=[module_path(PREFIX+m) for m in MODULES]
    if len(paths)!=len(set(paths)) or set(paths)!=set(SOURCE.rglob('*.lean')):
        raise ValueError('Missing or unregistered closed-quantile module')
    ordered=dependency_order(paths)
    if [p for p in ordered if p in paths] != paths:
        raise ValueError('Invalid closed-quantile dependency order')
    for p in ordered:
        if FORBIDDEN.search(strip_comments(p.read_text(encoding='utf-8'))):
            raise ValueError('Forbidden proof escape in '+str(p))
    roots=[PREFIX+n for p in paths
           for n in DECLARATION.findall(strip_comments(p.read_text(encoding='utf-8')))]
    if len(roots)!=len(set(roots)) or not set(required)<=set(roots):
        raise ValueError('Duplicate or missing declaration root')
    return paths,ordered,set(roots)


def main() -> int:
    if hasattr(sys.stdout,'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake',default='lake')
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--cached-dependencies',action='store_true')
    args=parser.parse_args()
    paths,ordered,roots=validate_sources()
    rebuilt=paths if args.cached_dependencies else ordered
    cached=cached_artifact_hashes(ordered,rebuilt) if args.cached_dependencies else {}
    protected=set(ordered)|{Path(__file__).resolve(),FREEZE,
        ROOT/'tools/verify_blind_upper_components.py',ROOT/'tools/verify_tier6.py',
        ROOT/'tools/verify_entropy_tail_components.py',ROOT/'tools/verify_entropy_tail.py',
        LEAN/'lean-toolchain',LEAN/'lake-manifest.json',LEAN/'lakefile.toml'}
    hashes={p.relative_to(ROOT).as_posix():sha(p) for p in sorted(protected)}
    output=args.output_dir or ROOT/'.runtime/closed-quantile'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    output.mkdir(parents=True,exist_ok=False)
    audit=LEAN/'.audit/ClosedQuantile.lean'
    source=''.join('import '+PREFIX+m+'\n' for m in MODULES)+'\n'
    source+=''.join(f'example : {t} := {d}\n' for d,t in EXACT_TARGETS.items())
    source+='\n'+''.join('#print axioms '+r+'\n' for r in sorted(roots))
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source,encoding='utf-8')
    (output/'ExactAudit.lean').write_text(source,encoding='utf-8')
    audit_hash=sha(audit)
    status=dict(valid=False,scope=SCOPE,source_sha256=hashes,
        cached_dependency_artifact_sha256=cached,audit_source_sha256=audit_hash,
        exact_targets=EXACT_TARGETS,exact_targets_checked=0,roots=sorted(roots),
        closed_quantile_law_verified=False,direct_finite_law_proof_verified=False,
        paper_explicit_lower_constant_verified=False,
        local_dependency_rebuild_performed=not args.cached_dependencies,
        module_count=len(paths),rebuilt_local_modules=len(rebuilt),commands=[])

    def save():
        (output/'status.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')

    save()
    commands=[]
    for path in rebuilt:
        rel=path.relative_to(LEAN)
        obj=Path('.lake/build/lib/lean')/rel.with_suffix('.olean')
        (LEAN/obj).parent.mkdir(parents=True,exist_ok=True)
        commands.append([args.lake,'env','lean','-j','1','-o',str(obj),str(rel)])
    commands.append([args.lake,'env','lean','-j','1',str(audit.relative_to(LEAN))])
    for i,command in enumerate(commands,1):
        result=subprocess.run(command,cwd=LEAN,capture_output=True,text=True,encoding='utf-8')
        report=result.stdout+result.stderr
        (output/f'{i:03d}.log').write_text(report,encoding='utf-8')
        status['commands'].append(dict(command=command,exit_code=result.returncode))
        save()
        print(f'{i}/{len(commands)} {command[-1]}: exit {result.returncode}',flush=True)
        if result.returncode:
            print(report,flush=True)
            return result.returncode
    status['axioms']=validate_reports(report,result.returncode,roots)
    validate_sources()
    validate_stability(hashes|cached,audit,audit_hash)
    status.update(valid=True,closed_quantile_law_verified=True,
                  exact_targets_checked=len(EXACT_TARGETS),declaration_count=len(roots))
    save()
    print(json.dumps(dict(valid=True,modules=len(paths),declarations=len(roots),
                          closed_quantile_law_verified=True,evidence=str(output))),flush=True)
    return 0


if __name__=='__main__':
    raise SystemExit(main())
