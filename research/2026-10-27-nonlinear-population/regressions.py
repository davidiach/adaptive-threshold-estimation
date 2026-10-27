"""Run unchanged validation regressions; preserve a separate checkpoint log."""
from pathlib import Path
import json, subprocess, sys, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
out=HERE/'regressions'
out.mkdir(exist_ok=True)
record=out/'RESULT.json'
if record.exists():raise RuntimeError('Refuse to overwrite completed regression checkpoint')
rows=[]
for path in ['tools/test_validation.py','tools/test_tier3_validation.py',
             'tools/test_tier4_validation.py','tools/test_tier5_validation.py','tools/verify_inputs.py']:
    start=time.perf_counter()
    p=subprocess.run([sys.executable,path],cwd=ROOT,capture_output=True,text=True,encoding='utf-8',timeout=180)
    (out/(Path(path).stem+'.log')).write_text(p.stdout+p.stderr,encoding='utf-8')
    rows.append(dict(command=[sys.executable,path],exit_code=p.returncode,seconds=time.perf_counter()-start))
    print(path,p.returncode,flush=True)
record.write_text(json.dumps(dict(valid=all(r['exit_code']==0 for r in rows),commands=rows),indent=2)+'\n')
if not all(r['exit_code']==0 for r in rows):raise SystemExit(1)
