"""Create the isolated, verified branch without changing the shared checkout.

Does not push. Uses a private temporary index, the pinned base, and only the
explicit sealed package paths. Ref creation refuses to replace any branch.
"""
from pathlib import Path
import hashlib,json,os,subprocess,uuid
from datetime import datetime,timezone

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE='a8a8dc49115aabdd1fba8d53d3390eb0a5eee864'
BRANCH='research/population-step-20261027'
PREFIX=HERE.relative_to(ROOT).as_posix()+'/'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,env=None,input=None):
    p=subprocess.run(['git',*args],cwd=ROOT,env=env,input=input,text=True,capture_output=True,encoding='utf-8')
    if p.returncode:raise RuntimeError(p.stderr+p.stdout)
    return p.stdout.strip()

def main():
    acceptance=json.loads((HERE/'ACCEPTANCE.json').read_text())
    assert acceptance['valid']
    checkpoint=HERE/'CHECKPOINT_SHA256.json'
    assert sha(checkpoint)==acceptance['checkpoint_sha256']
    sealed=json.loads(checkpoint.read_text())['files']
    assert all(sha(HERE/p)==h for p,h in sealed.items())
    # A reference must not exist: do not rewrite user history, even locally.
    assert subprocess.run(['git','show-ref','--verify','--quiet','refs/heads/'+BRANCH],cwd=ROOT).returncode==1
    shared_head=run(['rev-parse','HEAD'])
    index_name=Path(run(['rev-parse','--git-path','index']))
    if not index_name.is_absolute():index_name=ROOT/index_name
    index_sha=sha(index_name)
    private=HERE/'scratch'/('publish-'+uuid.uuid4().hex+'.index')
    private.parent.mkdir(exist_ok=True)
    env=dict(os.environ,GIT_INDEX_FILE=str(private))
    run(['read-tree',BASE],env)
    paths=sorted(set(sealed)|{'CHECKPOINT_SHA256.json','ACCEPTANCE.json'})
    # Force only this explicit list; ignored rendering/font/scratch files never enter it.
    for offset in range(0,len(paths),40):run(['add','-f','--',*[PREFIX+p for p in paths[offset:offset+40]]],env)
    changed=run(['diff','--cached','--name-only',BASE],env).splitlines()
    assert changed and all(p.startswith(PREFIX) for p in changed)
    tree=run(['write-tree'],env)
    message='research: verify single-coin obstruction and isolate population information gap\n\nAudit the inherited small-bias product theorem; prove the directional direct sum, radial counterexample and calibrated submodel upper, and fixed-feature pilot restriction. Preserve exact finite diagnostics and independent audits. The unrestricted minimax problem remains open.\n'
    commit=run(['commit-tree',tree,'-p',BASE],env,input=message)
    run(['update-ref','refs/heads/'+BRANCH,commit,'0'*40])
    assert sha(index_name)==index_sha,'Shared index changed concurrently; inspect before publication'
    receipt=dict(commit=commit,branch=BRANCH,parent=BASE,shared_head_before=shared_head,shared_head_after=run(['rev-parse','HEAD']),shared_index_unchanged=True,files_added=len(changed),scope=PREFIX,utc=datetime.now(timezone.utc).isoformat(),pushed=False)
    (HERE/'PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))

if __name__=='__main__':main()
