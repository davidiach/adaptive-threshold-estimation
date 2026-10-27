"""Summarize the frozen exploratory data; no selection or retuning."""
from pathlib import Path
import csv,hashlib,json,math,statistics
from collections import defaultdict
HERE=Path(__file__).resolve().parent
groups=defaultdict(list)
with (HERE/'RAW.csv').open() as file:
    for row in csv.DictReader(file):
        for k in ['rho','theta','estimate','clipped','seconds']:row[k]=float(row[k])
        for k in ['budget','replicate','work','max_depth','coins']:row[k]=int(row[k])
        groups[(row['law'],row['rho'],row['profile'],row['budget'],row['mode'])].append(row)
summary=[]
for key,rows in groups.items():
    law,rho,profile,budget,mode=key;n=len(rows);assert n==32
    theta=rows[0]['theta'];errors=[r['estimate']-theta for r in rows]
    mse=statistics.mean(e*e for e in errors);bias=statistics.mean(errors)
    variance=statistics.mean((e-bias)**2 for e in errors)
    clipped=statistics.mean((r['clipped']-theta)**2 for r in rows)
    assert abs(mse-variance-bias*bias)<1e-14
    assert all(r['work']==budget for r in rows)
    rad=rho*rho*math.sqrt(math.log(40)/(2*n))
    summary.append(dict(law=law,rho=rho,profile=profile,budget=budget,mode=mode,n=n,theta=theta,
        mse=mse,rmse=math.sqrt(mse),clipped_rmse=math.sqrt(clipped),bias=bias,variance=variance,
        miss_accuracy=statistics.mean(abs(e)>rho/4 for e in errors),
        mse_hoeffding95_low=max(0,mse-rad),mse_hoeffding95_high=min(rho*rho,mse+rad),
        mean_work=budget,median_work=budget,p90_work=budget,p99_work=budget,
        mean_seconds=statistics.mean(r['seconds'] for r in rows),
        mean_max_depth=statistics.mean(r['max_depth'] for r in rows),max_observed_depth=max(r['max_depth'] for r in rows),
        mean_coins=statistics.mean(r['coins'] for r in rows),
        zero_mse=theta*theta,half_mse=(.5-theta)**2,rarity_midpoint_mse=(rho/2-theta)**2))
path=HERE/'SUMMARY.csv'
if path.exists():raise RuntimeError('Do not overwrite analysis')
with path.open('w',newline='') as file:
    writer=csv.DictWriter(file,fieldnames=list(summary[0]));writer.writeheader();writer.writerows(summary)
cells=[]
for row in summary:
    if row['mode']!='feedback':continue
    same=[r for r in summary if all(r[k]==row[k] for k in ['law','rho','profile','budget'])]
    best=min((r for r in same if r['mode']!='feedback'),key=lambda x:x['mse'])
    cells.append(dict(law=row['law'],rho=row['rho'],profile=row['profile'],budget=row['budget'],feedback_mse=row['mse'],best_fixed_mse=best['mse'],best_fixed_mode=best['mode'],feedback_smaller=row['mse']<best['mse'],beats_rarity_midpoint=row['mse']<row['rarity_midpoint_mse']))
worst=[]
for law in sorted({r['law'] for r in summary}):
    for rho in sorted({r['rho'] for r in summary}):
        for budget in sorted({r['budget'] for r in summary}):
            subset=[r for r in summary if (r['law'],r['rho'],r['budget'])==(law,rho,budget)]
            risks={mode:max(r['mse'] for r in subset if r['mode']==mode) for mode in ['feedback','fresh','block4','block16']}
            worst.append(dict(law=law,rho=rho,budget=budget,maximum_tested_mse=risks,best_fixed_maximum=min(v for k,v in risks.items() if k!='feedback'),feedback_smaller=risks['feedback']<min(v for k,v in risks.items() if k!='feedback')))
record=dict(status='NUMERICAL exploratory float64; not minimax certification',complete=True,rows=sum(map(len,groups.values())),cells=len(cells),
    total_flips=sum(r['work'] for rows in groups.values() for r in rows),
    feedback_point_wins=sum(r['feedback_smaller'] for r in cells),
    feedback_beats_rarity_midpoint=sum(r['beats_rarity_midpoint'] for r in cells),
    maximum_tested_risk_point_wins=sum(r['feedback_smaller'] for r in worst),
    worst_case_groups=worst,comparisons=cells,
    uncertainty='Per-cell95% Hoeffding bounds for bounded squared loss under ideal independent simulation streams; not simultaneous, not coverage of an estimator-supplied interval. Python PRNG and float64 are numerical approximations.32 replicates yield wide bounds.',
    timing='Rows share a predictive cache, and omit Model setup. Overall experiment seconds include setup and all simulation. No one-shot speedup or amortized break-even claim.',
    verdict='REJECTED as evidence of uniform rare-event optimality or practical superiority; finite-prior heuristic and finite noisy stress suite cannot establish either.',
    raw_sha256=hashlib.sha256((HERE/'RAW.csv').read_bytes()).hexdigest(),summary_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
(HERE/'EXPERIMENT_REPORT.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['rows','total_flips','cells','feedback_point_wins','feedback_beats_rarity_midpoint','maximum_tested_risk_point_wins','verdict']}))
for row in worst:
    if row['budget']==1024:print(json.dumps(row))
