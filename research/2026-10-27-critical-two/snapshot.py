"""Read-only baseline capture; outputs stay in this research directory."""
from pathlib import Path
import hashlib,json,subprocess,sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def main():
    target=HERE/'BASELINE.json'
    if target.exists():
        raise SystemExit('Refusing to overwrite the initial baseline')
    tracked=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')
    special=['TIER5_FROZEN.sha256','tools/tier5_targets.json','tools/verify_tier5.py',
             'research/2026-10-27-minimax-audit/theorem/critical.tex']
    paths=sorted(set(filter(None,tracked+special)))
    hashes={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths if (ROOT/p).is_file()}
    record={'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
            'status':subprocess.check_output(['git','status','--short'],cwd=ROOT).decode(),
            'sha256':hashes,'scope':'Observed current bytes; not a lock on other agents editable work'}
    target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(f'Recorded {len(hashes)} current paths; no original source or evidence writes.')

if __name__=='__main__':main()
