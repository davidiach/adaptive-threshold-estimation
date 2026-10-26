"""Held-out summaries and descriptive bootstrap intervals (not coverage theorems)."""
from pathlib import Path
import csv,json
import numpy as np
ROOT=Path(__file__).resolve().parents[1];RES=ROOT/'results'
rng=np.random.default_rng(20261027);rows=[]
for stem in ['test','extension']:
    meta=json.loads((RES/f'{stem}.json').read_text());raw=np.load(RES/f'{stem}_raw.npz')
    for r in meta['rows']:
        key=f"{r['method']}_{r['budget']}";v=raw[key+'_value'];c=raw[key+'_work'];vc=np.clip(v,0,1)
        inds=rng.integers(0,len(v),size=(3000,len(v)))
        boot=np.sqrt(np.mean((vc[inds]-.025)**2,axis=1))
        q=np.quantile(boot,[.025,.975]);rr=dict(r);rr.update(rmse_ci_low=float(q[0]),rmse_ci_high=float(q[1]),interval_type='3000-resample percentile bootstrap; descriptive, no heavy-tail coverage guarantee')
        rows.append(rr)
(RES/'benchmark_summary.json').write_text(json.dumps(rows,indent=2))
fields=['method','budget','n','mean_work','work_se','rmse','rmse_ci_low','rmse_ci_high','rmse_raw','bias','clipped_fraction','work_p95','work_max']
with (RES/'benchmark_summary.csv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore');writer.writeheader();writer.writerows(rows)
print('Held-out rows',len(rows))
for r in rows:
 print(r['method'],r['budget'],round(r['mean_work'],1),tuple(round(r[x],5) for x in ['rmse','rmse_ci_low','rmse_ci_high']))
