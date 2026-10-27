"""Reproduce already opened baseline evidence; this is not new held-out data."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'.runtime/python'),str(ROOT/'benchmark')]
import numpy as np
import reference as ref
from real_threshold import real_replicates

def main():
    spec=json.loads((ROOT/'results/real_selection.json').read_text())
    training=json.loads((ROOT/'benchmark/data/training.json').read_text())['training']
    expected=np.load(ROOT/'results/real_test_raw.npz')
    out=[]
    for row in spec['rows']:
        b=row['budget'];bi=ref.BUDGETS.index(b)
        for name,mi in [('gha_tuned',1),('real_tuned',4)]:
            t=time.perf_counter();seed=41000+100*bi+mi;ref.seed_rng(seed)
            if mi==1:
                cfg=row['gha']['config'];levels,counts,planned=ref.allocate(b,training,'gha_'+str(row['gha']['index']))
                v,c=ref.gha_replicates(levels,counts,**cfg,reps=500)
            else:
                chosen=row['candidate'];v,c=real_replicates(**chosen['config'],probabilities=np.array(chosen['probabilities']),reps=500)
            result=dict(method=name,budget=b,seed=seed,replications=500,values_exact=bool(np.array_equal(v,expected[f'{name}_{b}_value'])),
                costs_exact=bool(np.array_equal(c,expected[f'{name}_{b}_work'])),seconds=time.perf_counter()-t,work=int(c.sum()),**ref.summarize(v,c))
            out.append(result);print(json.dumps(result),flush=True)
            (HERE/'BASELINE_BENCHMARK_REPLAY.json').write_text(json.dumps(out,indent=2)+'\n')
    assert all(r['values_exact'] and r['costs_exact'] for r in out)

if __name__=='__main__':main()
