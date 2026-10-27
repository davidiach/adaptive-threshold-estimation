"""Replay one predesignated replicate in every frozen cell; no retuning."""
from pathlib import Path
import csv,hashlib,json,time
import feedback_experiment as engine
HERE=Path(__file__).resolve().parent
path=HERE/'REPLAY.json'
if path.exists():raise RuntimeError('Refuse to overwrite replay')
start=time.perf_counter();checks=[];models={}
for li,law in enumerate(engine.LAWS):
    for ri,rho in enumerate(engine.RHOS):models[(law['name'],rho)]=(li,ri,engine.Model(law,rho))
with (HERE/'RAW.csv').open() as file:
    for row in csv.DictReader(file):
        if int(row['replicate'])!=0:continue
        li,ri,model=models[(row['law'],float(row['rho']))]
        profiles=model.profiles();pi=list(profiles).index(row['profile']);q=profiles[row['profile']]
        seed=2026102700+100000000*li+10000000*ri+100000*pi
        reservoir=engine.Reservoir(model.d,model.mass,q,seed)
        value,depth,coins=engine.estimate(model,reservoir.flip,int(row['budget']),row['mode'])
        error=abs(value-float(row['estimate']))
        assert error<1e-14 and depth==int(row['max_depth']) and coins==int(row['coins']) and reservoir.work==int(row['work'])
        checks.append(dict(law=row['law'],rho=row['rho'],profile=row['profile'],budget=row['budget'],mode=row['mode'],absolute_replay_difference=error,work=reservoir.work))
assert len(checks)==240
path.write_text(json.dumps(dict(valid=True,cells=len(checks),charged_replay_flips=sum(r['work'] for r in checks),seconds=time.perf_counter()-start,checks=checks,
    source_sha256=hashlib.sha256((HERE/'feedback_experiment.py').read_bytes()).hexdigest(),raw_sha256=hashlib.sha256((HERE/'RAW.csv').read_bytes()).hexdigest()),indent=2)+'\n')
print(json.dumps(dict(valid=True,cells=len(checks),seconds=time.perf_counter()-start)))
