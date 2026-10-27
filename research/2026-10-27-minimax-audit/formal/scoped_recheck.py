"""Separate follow-up audit after concurrent unrelated Tier5 source edits.

The original broad replay and its failed global stability result are preserved.
This audit only accepts roots whose entire local import closure is byte-identical
to the pre-build snapshot, and freshly re-elaborates the same exact-type/axiom
audit. Existing locks and validator functions are used without alteration.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
LEAN=ROOT/"lean"
sys.path.insert(0,str(ROOT/"tools"))
import verify_tier3 as guard

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    prior=json.loads((HERE/"replay.json").read_text())
    audit=HERE/"CurrentSourceAudit.lean"
    if sha(audit)!=prior["audit_source_sha256"]:
        raise RuntimeError("Audit source changed")
    code=audit.read_text(encoding="utf-8")
    modules=re.findall(r"^import (ThresholdHC[\w.]*)$",code,re.M)
    expected=set(re.findall(r"^#print axioms ([\w.']+)$",code,re.M))
    if len(expected)!=prior["expected_roots"]:
        raise RuntimeError("Root count mismatch")
    built={r["command"][-1] for r in prior["commands"]
           if len(r["command"])>=3 and r["command"][-2]=="build" and r["exit_code"]==0}
    if set(modules)!=built:
        raise RuntimeError("Previous successful module build coverage mismatch")
    closure=set()
    for module in modules:
        closure.update(guard.local_import_closure(module,ROOT))
    before={rel:sha(ROOT/rel) for rel in sorted(closure)}
    if any(prior["source_sha256"].get(rel)!=digest for rel,digest in before.items()):
        raise RuntimeError("An actually imported source changed since the build snapshot")
    for rel,digest in prior["locked_sha256"].items():
        if sha(ROOT/rel)!=digest:
            raise RuntimeError("Original lock mismatch: "+rel)
    differences=[rel for rel,digest in prior["source_sha256"].items()
                 if sha(ROOT/rel)!=digest]
    if set(differences)&closure:
        raise RuntimeError("Concurrent changes touch audited dependency closure")
    record={"valid":False,"scope":"Exact imported dependency closure only; not concurrent Tier5",
            "previous_global_audit_valid":prior["valid"],
            "previous_global_audit_file_sha256":sha(HERE/"replay.json"),
            "head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),
            "source_sha256":before,"excluded_concurrent_changes":differences,
            "expected_roots":len(expected),"original_locks_verified":True,
            "successful_build_modules":sorted(built)}
    env=dict(os.environ,ELAN_HOME=str(ROOT/".runtime/elan"),PYTHONUTF8="1")
    command=[str(ROOT/".runtime/elan/bin/lake.exe"),"env","lean",str(audit)]
    start=time.time()
    result=subprocess.run(command,cwd=LEAN,env=env,capture_output=True,text=True,encoding="utf-8",timeout=900)
    output=result.stdout+result.stderr
    (HERE/"scoped_recheck.log").write_text(output,encoding="utf-8")
    reports=guard.parse_reports(output)
    unchanged=all(sha(ROOT/rel)==digest for rel,digest in before.items())
    unchanged=unchanged and all(sha(ROOT/rel)==digest for rel,digest in prior["locked_sha256"].items())
    ok=guard.valid_audit(result.returncode,reports,expected,unchanged)
    record.update(valid=ok,complete=ok,command=command,cwd=str(LEAN),exit_code=result.returncode,
                  seconds=time.time()-start,reports=reports,actual_roots=len(reports),
                  sources_and_locks_unchanged=unchanged,
                  axiom_union=sorted(set(a for xs in reports.values() for a in xs)))
    (HERE/"scoped_recheck.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:record[k] for k in ["valid","complete","actual_roots","expected_roots","axiom_union"]}))
    return 0 if ok else 1

if __name__=="__main__":
    raise SystemExit(main())
