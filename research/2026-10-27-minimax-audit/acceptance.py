"""Read-only preservation/lock checks and new-checkpoint evidence validation.

Writes only ACCEPTANCE.json in this new directory. Does not bless concurrent
Tier5 sources or rewrite historical manifests.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'.runtime/python'))
import numpy as np

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    baseline=json.loads((HERE/'BASELINE_SNAPSHOT.json').read_text())
    protected={p:h for p,h in baseline['files'].items() if p.startswith(('inputs/','paper/','constants/','benchmark/','results/','tools/','lean/')) or p.endswith('FROZEN.sha256')}
    protected={p:h for p,h in protected.items() if not p.startswith('lean/ThresholdHC/Tier5/') and p!='paper/UPDATES.md'}
    changed=[p for p,h in protected.items() if not (ROOT/p).is_file() or sha(ROOT/p)!=h]
    # Keep the original all-protected-files criterion and record its failure.
    # Continue independent checks even when concurrent outputs drifted.
    assert (ROOT/'paper/paper.tex').read_bytes()==(ROOT/'inputs/next-phase/baseline/Adaptive_Threshold_v4/source/paper.tex').read_bytes()
    assert (ROOT/'paper/paper.pdf').read_bytes()==(ROOT/'inputs/next-phase/baseline/Adaptive_Threshold_v4/Distributional_Minimax_Law_Adaptive_Threshold_Estimation_v4.pdf').read_bytes()
    records=json.loads((HERE/'BASELINE_RUNS.json').read_text());assert len(records)==14 and all(r['exit']==0 for r in records)
    replay=json.loads((HERE/'BASELINE_BENCHMARK_REPLAY.json').read_text());assert len(replay)==4 and all(r['values_exact'] and r['costs_exact'] for r in replay)
    prereg=json.loads((HERE/'PREREGISTRATION.json').read_text());assert sha(HERE/'experiments.py')==prereg['source_sha256']
    marker=json.loads((HERE/'TEST_STARTED.json').read_text());assert marker['prereg_sha256']==sha(HERE/'PREREGISTRATION.json')
    data=json.loads((HERE/'BENCHMARK_RESULTS.json').read_text());assert data['complete'] and len(data['rows'])==42
    raw=np.load(HERE/'BENCHMARK_RAW.npz',allow_pickle=False);assert len(raw.files)==126
    for r in data['rows']:
        model=next(m['id'] for m in prereg['models'] if m['name']==r['model'])
        method=prereg['methods'].index(r['method']);key=f"{model}_{r['budget']}_{method}"
        v=raw[key+'_value'];c=raw[key+'_work'];outer=raw[key+'_outer'];assert len(v)==128 and len(c)==128 and len(outer)==128
        assert abs(float(np.sqrt(np.mean((np.clip(v,0,1)-r['theta'])**2)))-r['clipped']['rmse'])<1e-14
        assert int(c.sum())==r['work_total'] and int(outer.sum())==r['outer_total']
    assert sum(r['work_total'] for r in data['rows'])==data['total_work']
    for lockpath,key in [(HERE/'formal/MODEL_EXTENSION_LOCK_v1.json','locked_sha256')]:
        lock=json.loads(lockpath.read_text())
        for rel,h in lock[key].items():assert sha(lockpath.parent/rel)==h,(rel,'lock changed')
    paperlock=json.loads((HERE/'PAPER_CHECKPOINT_LOCK_v1.json').read_text())
    for rel,h in paperlock['sha256'].items():assert sha(HERE/rel)==h,(rel,'paper checkpoint changed')
    scoped=json.loads((HERE/'formal/scoped_recheck.json').read_text())
    assert scoped['valid'] and scoped['complete']
    required=['STATE.md','CLAIMS.tsv','RESEARCH_NOTE.tex','RESEARCH_NOTE.pdf','LITERATURE_AUDIT.md','ALGORITHMS.md','FORMAL_COVERAGE.md','FAILED_APPROACHES.md','REVIEW_PACKET.md','FINAL_REPORT.md','DEPENDENCIES.md','RUN_LOG.md']
    assert all((HERE/p).is_file() for p in required)
    log=(HERE/'logs/latex-final.log').read_text(encoding='utf-8-sig')
    assert 'Writing' in log and 'RESEARCH_NOTE.pdf' in log and 'Overfull' not in log
    out=dict(valid=not changed,head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
        global_protected_byte_preservation=not changed,changed_existing_files=changed,
        changed_existing_hashes={p:dict(initial=protected[p],current=sha(ROOT/p)) for p in changed},other_deliverable_checks_passed=True,
        protected_existing_files_checked=len(protected),protected_existing_files_unchanged=len(protected)-len(changed),v4_tex_and_pdf_match_inputs=True,baseline_gates=14,historical_reproduced_runs=2000,new_final_cells=42,new_final_runs=5376,
        new_final_observations=data['total_work'],preregistration_unchanged=True,new_paper_spec_lock_checked=True,
        formal_scope='See scoped_recheck.json; new statistical theorems not Lean checked; concurrent Tier5 excluded',
        final_artifact_sha256={p:sha(HERE/p) for p in required},
        visual_review='12-page contact sheet plus full-resolution pages3,8,12 inspected; no clipping/overlap observed; fontconfig renderer warnings retained',
        limitations='Arbitrary-law minimax unresolved; no novelty certification or practical superiority; no external review')
    (HERE/'ACCEPTANCE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
    return 0 if not changed else 1

if __name__=='__main__':raise SystemExit(main())
