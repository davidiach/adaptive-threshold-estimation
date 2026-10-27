from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    dest=HERE/'inherited';dest.mkdir(exist_ok=True)
    files=['research/2026-10-27-critical-two/construction.tex','research/2026-10-27-critical-two/review.md','research/2026-10-27-critical-two/sources.md','research/2026-10-27-critical-two/alternative.md','research/2026-10-27-minimax-audit/theorem/critical.tex']
    records=[]
    for rel in files:
        src=ROOT/rel;target=dest/(('upper-' if 'minimax-audit' in rel else '')+src.name)
        if target.exists():raise RuntimeError('Refusing to replace inherited snapshot '+str(target))
        data=src.read_bytes();target.write_bytes(data)
        records.append(dict(source=rel,snapshot=str(target.relative_to(HERE)).replace('\\','/'),sha256=hashlib.sha256(data).hexdigest()))
    out=dict(head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),status=subprocess.check_output(['git','status','--short'],cwd=ROOT).decode(),files=records,
        contract_sha256=sha(HERE/'CONTRACT.md'),note='Inherited work pinned before this run; no priority or external-review assertion')
    (HERE/'BASELINE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
