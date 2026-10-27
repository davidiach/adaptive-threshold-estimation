"""Current-byte baseline audit; never writes into historical results."""
from pathlib import Path
import hashlib, json, os, platform, shutil, subprocess, sys, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SNAP = ROOT.parent / 'minimax-baseline-snapshot'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT).decode('utf-8').strip()

def main():
    if SNAP.exists():
        raise SystemExit('Refusing to overwrite snapshot '+str(SNAP))
    SNAP.mkdir()
    files = subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=ROOT).decode().split('\0')
    hashes = {}
    for rel in sorted(set(filter(None, files))):
        if rel.startswith('research/2026-10-27-minimax-audit/'):
            continue
        src = ROOT / rel
        if not src.is_file(): continue
        data=src.read_bytes(); dest=SNAP/rel
        dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        hashes[rel]=hashlib.sha256(data).hexdigest()
    sys.path.insert(0,str(ROOT/'.runtime/python'))
    import numpy, scipy, numba, mpmath, llvmlite
    meta=dict(head=git('rev-parse','HEAD'),branch=git('branch','--show-current'),
        status=git('status','--short'),remote=git('remote','-v'),snapshot=str(SNAP),
        python=sys.version,platform=platform.platform(),versions={m.__name__:m.__version__ for m in [numpy,scipy,numba,mpmath,llvmlite]},files=hashes)
    (HERE/'BASELINE_SNAPSHOT.json').write_text(json.dumps(meta,indent=2)+'\n')
    commands=[['tools/verify_inputs.py'],['tools/verify_experiment_lock.py'],
        ['tools/freeze.py','--verify'],['tools/check_targets_numeric.py'],
        ['tools/check_targets2_numeric.py'],['-m','unittest','discover','-s','tools','-p','test_*.py','-v'],
        ['tools/check_power_bracket.py'],['proposals/constants/bias_audit.py'],
        ['proposals/constants/uniform_constant_checks.py'],['constants/score_constants.py','constants/candidate_theory.json'],
        ['constants/score_constants.py','constants/candidate_finite_grid.json'],['constants/score_constants.py','constants/candidate.json'],
        ['benchmark/verify_real.py'],['research/2026-10-27-route-a/check_construction.py']]
    env=dict(os.environ,PYTHONUTF8='1',PYTHONPATH=str(ROOT/'.runtime/python'))
    logdir=HERE/'logs';logdir.mkdir(exist_ok=True);records=[]
    for i,args in enumerate(commands):
        t=time.perf_counter()
        try:
            proc=subprocess.run([sys.executable,*args],cwd=SNAP,env=env,capture_output=True,text=True,encoding='utf-8',timeout=180)
            code=proc.returncode; output=proc.stdout+proc.stderr
        except subprocess.TimeoutExpired as e:
            code=124;output='TIMEOUT after 180 seconds\n'+str(e.stdout)+str(e.stderr)
        name=f'baseline-{i+1:02d}.log';(logdir/name).write_text(output,encoding='utf-8')
        rec=dict(command=[sys.executable,*args],cwd=str(SNAP),exit=code,seconds=time.perf_counter()-t,log='logs/'+name)
        records.append(rec);print(json.dumps(rec),flush=True)
        (HERE/'BASELINE_RUNS.json').write_text(json.dumps(records,indent=2)+'\n')
    return max(r['exit'] for r in records)

if __name__=='__main__': raise SystemExit(main())
