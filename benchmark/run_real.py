"""Train, tune, lock, and once-only test the direct-real candidate.

Existing GHA training/tuning are reused byte-for-byte. New stages use independent
seed families (12000 train, 32000 tune); final test adds method index 4 to the
original 41000+budget_index*100+method_index formula. GHA retains index 1.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCAL = ROOT/'.runtime'/'python'
if LOCAL.exists():
    sys.path.insert(0, str(LOCAL))
import numpy as np
import numba
import scipy
import reference as ref
from real_threshold import train_level, level_count, real_replicates

RES = ROOT/'results'
DATA = Path(__file__).resolve().parent/'data'
BUDGETS = [16384, 65536]
CONFIGS = [dict(start=s, ratio=r, threshold=t)
           for s in [16,64,256] for r in [2,4] for t in [.5,1.,1.5]]
CONFIGS += [dict(start=s,ratio=r,threshold=t,antithetic=True)
            for s in [64,256,1024] for r in [2,4] for t in [.5,1.,1.5]]
CONFIGS += [dict(start=s,ratio=r,threshold=t,sum_mode=True)
            for s in [16,64,256,1024] for r in [2,4] for t in [.5,1.,1.5]]
CONFIGS += [dict(start=s,ratio=4,threshold=t,sum_mode=True,repeats=4)
            for s in [64,256,1024] for t in [.5,1.,1.5]]
LAW_NAMES = ['trained','geometric_half','geometric_three_quarters']


def save(name, value):
    (RES/name).write_text(json.dumps(value, indent=2)+'\n', encoding='utf-8')


def train(n):
    if (RES/'real_selection.json').exists():raise RuntimeError('Selection locked; training is closed.')
    t0, rows, total = time.time(), [], 0
    if (RES/'real_training.json').exists():
        previous=json.loads((RES/'real_training.json').read_text())
        rows,total=previous['rows'],previous['total_work']
    for i, cfg in enumerate(CONFIGS):
        if any(row['index']==i and row['config']==cfg for row in rows):continue
        if cfg.get('sum_mode'):
            rows.append(dict(index=i,config=cfg,levels=[],note='fixed geometric law; no offline moment fit'))
            continue
        ref.seed_rng(12000+i)
        levels = []
        for j in range(level_count(max(BUDGETS), cfg['start'], cfg['ratio'])):
            v,c = train_level(j, **cfg, reps=n)
            levels.append(dict(level=j,n=n,mean=float(v.mean()),second=float((v*v).mean()),work=float(c.mean()),total_work=int(c.sum())))
            total += int(c.sum())
        rows.append(dict(index=i,config=cfg,levels=levels))
        print('trained',i,cfg,'work',total,flush=True)
    out = dict(rows=rows,total_work=total,seconds=time.time()-t0,seed_formula='12000+config_index',replications=n)
    save('real_training.json',out)


def probabilities(cells, cfg, count, name):
    if name == 'trained':
        # Positive finite-sample floor prevents dropping a rarely observed level.
        weights = np.array([np.sqrt(max(c['second'],1/(4*c['n']))/c['work']) for c in cells[:count]])
    else:
        exponent = .5 if name == 'geometric_half' else .75
        weights = cfg['ratio']**(-exponent*np.arange(count,dtype=float))
    return weights/weights.sum()


def tune(n):
    if (RES/'real_selection.json').exists():raise RuntimeError('Selection locked; tuning is closed.')
    training = json.loads((RES/'real_training.json').read_text())
    rows, total, t0 = [], 0, time.time()
    if (RES/'real_tuning.json').exists():
        previous=json.loads((RES/'real_tuning.json').read_text())
        rows,total=previous['rows'],previous['total_work']
    for budget in BUDGETS:
        bi = ref.BUDGETS.index(budget)
        for cfgrow in training['rows']:
            cfg = cfgrow['config']
            count = level_count(budget/cfg.get('repeats',1),cfg['start'],cfg['ratio'])
            if cfg.get('repeats',1)>1 and count<2:continue
            for li, name in enumerate(LAW_NAMES):
                if cfg.get('sum_mode') and name=='trained':continue
                index = 3*cfgrow['index']+li
                if any(row['budget']==budget and row['index']==index and row['config']==cfg for row in rows):continue
                p = probabilities(cfgrow['levels'],cfg,count,name)
                seed = ((32000+bi*100+index) if index<54 else
                        (33000+bi*100+index-54) if index<108 else
                        (34000+bi*100+index-108) if index<180 else
                        (35000+bi*100+index-180))
                ref.seed_rng(seed)
                v,c = real_replicates(**cfg, probabilities=p, reps=n)
                total += int(c.sum())
                row = dict(index=index,budget=budget,config=cfg,law=name,probabilities=p.tolist(),seed=seed,**ref.summarize(v,c))
                rows.append(row)
                print('tune',budget,index,'rmse',round(row['rmse'],5),'work',round(row['mean_work']),flush=True)
                save('real_tuning.json',dict(rows=rows,total_work=total,seconds=time.time()-t0,complete=False,replications=n))
    save('real_tuning.json',dict(rows=rows,total_work=total,seconds=time.time()-t0,complete=True,replications=n,seed_formula='prefix: 32000+bi*100+index; antithetic: 33000+bi*100+index-54; randomized sum: 34000+bi*100+index-108; four-repeat sum: 35000+bi*100+index-180; bi is original budget index'))


def lock():
    if (RES/'real_selection.json').exists():
        raise RuntimeError('Selection already locked; do not overwrite it.')
    tuning = json.loads((RES/'real_tuning.json').read_text())
    if not tuning['complete']:
        raise RuntimeError('Incomplete tuning')
    original = json.loads((DATA/'tuning.json').read_text())
    rows=[]
    for b in BUDGETS:
        ours = min((r for r in tuning['rows'] if r['budget']==b),key=lambda r:r['rmse'])
        gha = min((r for r in original['rows'] if r['budget']==b and r['method']=='gha'),key=lambda r:r['rmse'])
        rows.append(dict(budget=b,candidate=ours,gha=gha))
    hashes={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('real_threshold.py'),Path(__file__).with_name('reference.py'),Path(__file__).with_name('verify_real.py'),RES/'real_verification.json',RES/'real_training.json',RES/'real_tuning.json',DATA/'training.json',DATA/'tuning.json']}
    save('real_selection.json',dict(rows=rows,hashes=hashes,heldout_replications=500,selection_rule='minimum clipped tuning RMSE per budget; 100 independent tuning repetitions per cell',baseline_zero_rmse=ref.THETA,test_seed_formula='41000+original_budget_index*100+method_index; GHA=1, direct_real=4',environment=dict(python=sys.version,numpy=np.__version__,scipy=scipy.__version__,numba=numba.__version__,platform=platform.platform())))
    print(json.dumps(rows,indent=2))


def intervals(v,c,seed):
    rng=np.random.default_rng(seed)
    ix=rng.integers(0,len(v),size=(3000,len(v)))
    errors=(np.clip(v,0,1)-ref.THETA)**2
    return dict(rmse_interval=np.quantile(np.sqrt(errors[ix].mean(axis=1)),[.025,.975]).tolist(),work_interval=np.quantile(c[ix].mean(axis=1),[.025,.975]).tolist())


def test():
    marker=RES/'real_test_started.json'
    if marker.exists():
        raise RuntimeError('Held-out test was already started; do not rerun or retune.')
    selection=json.loads((RES/'real_selection.json').read_text())
    for name,digest in selection['hashes'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
            raise RuntimeError('Selection input changed: '+name)
    marker.write_text(json.dumps(dict(selection_sha256=hashlib.sha256((RES/'real_selection.json').read_bytes()).hexdigest(),started=time.time()))+'\n')
    training=json.loads((DATA/'training.json').read_text())['training']
    n=selection['heldout_replications']
    rows,raw,t0=[],{},time.time()
    for spec in selection['rows']:
        b=spec['budget'];bi=ref.BUDGETS.index(b)
        for name,mi in [('gha_tuned',1),('real_tuned',4)]:
            seed=41000+bi*100+mi;ref.seed_rng(seed)
            if name=='gha_tuned':
                cfg=spec['gha']['config'];idx=spec['gha']['index']
                levels,counts,expected=ref.allocate(b,training,f'gha_{idx}')
                v,c=ref.gha_replicates(levels,counts,**cfg,reps=n)
                extra=dict(levels=levels.tolist(),counts=counts.tolist(),planned_work=expected)
            else:
                chosen=spec['candidate'];cfg=chosen['config']
                v,c=real_replicates(**cfg,probabilities=np.array(chosen['probabilities']),reps=n)
                extra=dict(law=chosen['law'],probabilities=chosen['probabilities'])
            raw[f'{name}_{b}_value']=v;raw[f'{name}_{b}_work']=c
            rows.append(dict(method=name,budget=b,seed=seed,config=cfg,**extra,**ref.summarize(v,c),**intervals(v,c,51000+bi*100+mi)))
            print(name,b,rows[-1]['rmse'],rows[-1]['mean_work'],flush=True)
            np.savez_compressed(RES/'real_test_raw.npz',**raw)
            save('real_test.json',dict(rows=rows,seconds=time.time()-t0,complete=False))
    save('real_test.json',dict(rows=rows,seconds=time.time()-t0,complete=True,total_work=sum(r['mean_work']*n for r in rows),replications=n,baseline_zero_rmse=ref.THETA,intervals='descriptive percentile bootstrap, 3000 resamples, not certified heavy-tail coverage',accept=all(next(r for r in rows if r['budget']==b and r['method']=='real_tuned')['rmse']<next(r for r in rows if r['budget']==b and r['method']=='gha_tuned')['rmse'] for b in BUDGETS)))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('stage',choices=['train','tune','lock','test'])
    parser.add_argument('--n',type=int)
    args=parser.parse_args()
    if args.stage=='train':train(args.n or 2000)
    elif args.stage=='tune':tune(args.n or 100)
    elif args.stage=='lock':lock()
    else:test()
