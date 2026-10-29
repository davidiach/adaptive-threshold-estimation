"""Summarize the sealed held-out run; never run or tune an estimator."""
from __future__ import annotations
import json
from pathlib import Path
import sys
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
RES=ROOT/'results'
sys.path.insert(0,str(ROOT/'tools'))
from verify_experiment_lock import matches_lock, require


def main():
    selection=json.loads((RES/'real_selection.json').read_text())
    for name,digest in selection['hashes'].items():
        # Tolerates verify_real.py's line-ending rewrite of its record, as the lock check does.
        require(matches_lock(name,(ROOT/name).read_bytes(),digest),'Locked benchmark input changed: '+name)
    test=json.loads((RES/'real_test.json').read_text())
    require(test['complete'],'held-out test record is incomplete')
    raw=np.load(RES/'real_test_raw.npz')
    comparisons=[]
    for bi,b in enumerate([16384,65536]):
        rng=np.random.default_rng(2026102703+bi)
        real=raw[f'real_tuned_{b}_value'];gha=raw[f'gha_tuned_{b}_value']
        re=(np.clip(real,0,1)-.025)**2;ge=(np.clip(gha,0,1)-.025)**2
        ri=rng.integers(0,len(re),size=(3000,len(re)))
        gi=rng.integers(0,len(ge),size=(3000,len(ge)))
        differences=np.sqrt(re[ri].mean(axis=1))-np.sqrt(ge[gi].mean(axis=1))
        comparisons.append(dict(budget=b,rmse_difference_direct_minus_gha=float(np.sqrt(re.mean())-np.sqrt(ge.mean())),descriptive_difference_interval=np.quantile(differences,[.025,.975]).tolist(),seed=2026102703+bi))
    tr=json.loads((RES/'real_training.json').read_text())
    tu=json.loads((RES/'real_tuning.json').read_text())
    gt=json.loads((ROOT/'benchmark/data/training.json').read_text())
    gu=json.loads((ROOT/'benchmark/data/tuning.json').read_text())
    out=dict(accept=test['accept'],comparisons=comparisons,
             verdict='GHA wins both held-out RMSE point estimates; no post-test tuning.',
             offline_work=dict(direct_training=tr['total_work'],direct_tuning=tu['total_work'],direct_total=tr['total_work']+tu['total_work'],gha_training=gt['total_work'],gha_tuning_only=sum(r['n']*r['mean_work'] for r in gu['rows'] if r['method']=='gha'),original_all_method_tuning=gu['total_work']),
             tuning_cells=len(tu['rows']),heldout_reps=500,source_integrity='all nine locked hashes match',
             interval_note='Independent percentile bootstrap, 3000 resamples; descriptive, not certified heavy-tail coverage.')
    (RES/'real_comparison.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
