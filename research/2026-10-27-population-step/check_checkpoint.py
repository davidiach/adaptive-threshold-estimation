"""Final scoped acceptance; preserves source checkpoints and old outputs."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,os,shutil,subprocess,sys,tempfile
from datetime import datetime,timezone

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE='a8a8dc49115aabdd1fba8d53d3390eb0a5eee864'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads((HERE/p).read_text(encoding='utf-8'))
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True,encoding='utf-8').strip()

def main():
    output=HERE/'ACCEPTANCE.json'
    seal=HERE/'CHECKPOINT_SHA256.json'
    if output.exists() or seal.exists():raise RuntimeError('Refuse to overwrite final checkpoint')
    checks={}
    hashes=read('audit/FINAL_PROOF_HASHES.json')['final_accepted_proof_sha256']
    checks['reviewed_paper_sources_match']=all(sha(HERE/p)==h for p,h in hashes.items())
    checks['inherited_snapshot_matches']=all(sha(HERE/r['snapshot'])==r['sha256'] for r in read('BASELINE.json')['files'])
    record=read('audit/tier5_replay.json')
    checks['tier5_actual_targets_and_roots']=record['valid'] and record['complete'] and len(record['targets'])==9 and record['actual_roots']==record['expected_roots']==109
    checks['tier5_standard_axioms']=record['axiom_union']==['Classical.choice','Quot.sound','propext']
    checks['tier5_snapshots_match']=all(sha(HERE/'audit/tier5-sources'/p)==h for p,h in record['source_sha256_before'].items())
    checks['tier5_live_sources_match']=all(sha(ROOT/p)==h for p,h in record['source_sha256_before'].items())
    # Independently verify the actual original lock bytes, including predecessors.
    lock_counts={}
    for name in ['FROZEN.sha256','TIER3_FROZEN.sha256','TIER4_FROZEN.sha256','TIER5_FROZEN.sha256']:
        count=0
        for line in (ROOT/name).read_text().splitlines():
            if not line.strip() or line.startswith('#'):continue
            expected,rel=line.split(maxsplit=1);p=(ROOT/rel).resolve()
            assert p.is_relative_to(ROOT.resolve())
            assert sha(p)==expected,(name,rel)
            count+=1
        lock_counts[name]=count
    checks['all_four_original_locks']=all(lock_counts.values())
    p=subprocess.run([sys.executable,'tools/verify_inputs.py'],cwd=ROOT,capture_output=True,text=True)
    checks['original_input_manifest']=p.returncode==0
    checks['regressions_passed']=read('regressions/RESULT.json')['valid']
    for file in ['audit/arithmetic_recheck.json','audit/small_bias_recheck.json']:
        data=read(file)
        if file.endswith('small_bias_recheck.json'):
            checks[file]=all(x is True for x in data['checks'].values())
        else:
            checks[file]=all(x['passed'] is True for x in data['checks'].values())
    pop=read('audit/population_recheck.json')
    checks['population_constants']=all(pop['constants'].values())
    checks['population_final_sources_match']=all(sha(ROOT/p)==h for p,h in pop['source_sha256_after'].items())
    checks['population_exact_cases']=len(pop['ruin_cases'])==32 and len(pop['three_flip_moment_cases'])==8
    upper=read('upper/exact_checks.json')
    checks['upper_exact_checks_passed']=upper['status']=='EXACT_RATIONAL_FINITE_CHECKS_PASSED'
    checks['upper_verified_implementation_match']=all(sha(HERE/'upper'/p)==upper['source_sha256'][p] for p in ['check_exact.py','two_gap_control.py','proof.tex'])
    spec=read('FINITE_LOCK.json')
    checks['finite_preregistered_lock']=sha(HERE/'finite_bayes.py')==spec['implementation_sha256'] and sha(HERE/'CONTRACT.md')==spec['contract_sha256']
    checks['independent_finite_check']=read('FINITE_VERIFY.json')['valid'] and len(read('FINITE_VERIFY.json')['checks'])==10
    scratch=HERE/'scratch';scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='replay-',dir=scratch) as directory:
        dest=Path(directory)
        for name in ['finite_bayes.py','verify_finite.py','FINITE_LOCK.json','CONTRACT.md']:shutil.copyfile(HERE/name,dest/name)
        logs=[]
        for script,arg in [('finite_bayes.py','run'),('verify_finite.py',None)]:
            cmd=[sys.executable,str(dest/script)]+([arg] if arg else [])
            run=subprocess.run(cmd,capture_output=True,text=True,timeout=60)
            logs.append(dict(script=script,exit_code=run.returncode,output=run.stdout+run.stderr))
            assert run.returncode==0,logs[-1]
        fresh=json.loads((dest/'FINITE_RESULTS.json').read_text())
        checks['finite_fresh_replay_exact']=fresh['rows']==read('FINITE_RESULTS.json')['rows']
        checks['policies_fresh_replay_exact']=all(json.loads((dest/(c+'_policy.json')).read_text())==read(c+'_policy.json') for c in ['two_scales','three_scales'])
    assembly=read('NOTE_ASSEMBLY.json')
    checks['paper_packaging_matches']=all(sha(HERE/r['source'])==r['source_sha256'] and sha(HERE/r['target'])==r['target_sha256'] for r in assembly['files'])
    log=(HERE/'RESEARCH_NOTE.log').read_text(encoding='utf-8')
    checks['pdf_compiled']= (HERE/'RESEARCH_NOTE.pdf').read_bytes().startswith(b'%PDF-')
    checks['pdf_no_overflow_or_unresolved_refs']='Overfull' not in log and 'undefined' not in log.lower()
    checks['required_deliverables']=all((HERE/name).is_file() for name in ['STATE.md','CLAIMS.tsv','RESEARCH_NOTE.tex','RESEARCH_NOTE.pdf','LITERATURE_AUDIT.md','ALGORITHMS.md','FORMAL_COVERAGE.md','FAILED_APPROACHES.md','REVIEW_PACKET.md','FINAL_REPORT.md','RUN_LOG.md','DEPENDENCIES.md'])
    excluded={'ACCEPTANCE.json','CHECKPOINT_SHA256.json','PUBLICATION_RECEIPT.json'}
    files={p.relative_to(HERE).as_posix():sha(p) for p in sorted(HERE.rglob('*')) if p.is_file() and p.name not in excluded and not any(x in {'rendered','scratch','__pycache__'} for x in p.relative_to(HERE).parts) and p.suffix not in {'.aux','.out','.toc'}}
    seal.write_text(json.dumps(dict(kind='POST-PROOF source and evidence checkpoint; not preregistration',files=files),indent=2)+'\n')
    result=dict(valid=all(checks.values()),scope='Verified new package and original locks; not a claim of arbitrary-law minimax completion or a clean shared checkout',utc=datetime.now(timezone.utc).isoformat(),base_commit=BASE,shared_head=git('rev-parse','HEAD'),shared_branch=git('branch','--show-current'),shared_status=git('status','--short'),publish_branch='research/population-step-20261027',checks=checks,lock_counts=lock_counts,inputs_output=p.stdout+p.stderr,finite_replay=logs,checkpoint_sha256=sha(seal),new_package_file_count=len(files),pdf_visual_review='20-page contact sheet; larger radial page8 and final changed page19 inspected; no clipping/overlap seen; two underfull source-path paragraph warnings remain')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(valid=result['valid'],checks=len(checks),new_package_files=len(files),shared_head=result['shared_head'])))
    if not result['valid']:raise SystemExit(1)

if __name__=='__main__':main()
