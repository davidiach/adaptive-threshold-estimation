"""Locked, bounded-size new confirmation suite. No fit or post-test selection."""
from pathlib import Path
import hashlib, json, math, os, sys, time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'.runtime/python'))
import numpy as np
from scipy.special import ndtri
from numba import njit

@njit(cache=True)
def state(model):
    u=np.random.random()
    if model<=1: return np.random.normal()
    if model==2: return .2 if u<.01 else -.2
    if model==3:
        if u<.04: return .01 if np.random.random()<.5 else -.01
        return -.25
    if model==4: return .25 if u<.05 else -.005
    if model==5: return np.random.random()-.95
    return .5 if u<.02 else -.5

@njit(cache=True)
def observation(model, hidden, loss):
    if model<=1:
        u=np.random.normal();z=np.random.normal()
        return .02*(hidden*hidden-u*u)+2*math.sqrt(.02*.98)*hidden*z-loss
    if model==5: return hidden+np.random.normal()
    return (1. if np.random.random()<.5+hidden else 0.)-.5

@njit(cache=True)
def decision(sm,ss,n,cap,factor):
    if n==cap:return int(sm>0)
    if n<16:return -1
    v=max(0.,(ss-sm*sm/n)/(n-1))
    b=math.sqrt(v*(1+math.log(cap/n))/n)
    if sm/n > factor*b:return 1
    if sm/n < -b:return 0
    return -1

@njit(cache=True)
def direct_term(model,loss,cap,rho,asymmetric):
    # Fixed two-level randomized sum, independent of the observations.
    prob=4.**(-.75)/(1+4.**(-.75));level=int(np.random.random()<prob)
    hidden=state(model);sm=0.;ss=0.;n=1;prev=0;zc=-1;zf=-1
    factor=math.sqrt(1+math.log(1/rho)) if asymmetric else 1.
    while True:
        for k in range(prev,n):
            x=observation(model,hidden,loss);sm+=x;ss+=x*x
        if zc<0:zc=decision(sm,ss,n,cap//4,factor)
        if level and zf<0:zf=decision(sm,ss,n,cap,factor)
        if zc>=0 and (not level or zf>=0):
            return (zc+(zf-zc)/prob if level else float(zc)),n
        prev=n;n*=2

@njit(cache=True)
def gha_term(model,loss,cap):
    # Algorithm 1 inner sample rule. Single base level, not a multilevel driver.
    n0=32;lev=0
    while n0*4**(lev+1)<=cap:lev+=1
    limit=n0*4**lev;n=n0*2**lev;cost=0;hidden=state(model)
    while True:
        if 2*n>=limit:n=limit;break
        sm=0.;ss=0.
        for k in range(n):
            x=observation(model,hidden,loss);sm+=x;ss+=x*x
        cost+=n;d=abs(sm/n);sigma=math.sqrt(max(0.,ss/n-(sm/n)**2))
        if sigma==0.:target=0. if d>0 else float(limit)
        elif d==0.:target=float(limit)
        else:target=limit*(math.sqrt(n0)*2**lev*d/(3*sigma))**(-1.5)
        if n>=target:break
        n*=2
    sm=0.
    for k in range(n):sm+=observation(model,hidden,loss)
    return (1. if sm>0 else 0.),cost+n

@njit(cache=True)
def term(model,loss,cap,rho,method):
    if method==0:return gha_term(model,loss,cap//2)
    return direct_term(model,loss,cap,rho,method==2)

@njit(cache=True)
def replicates(model,loss,budget,rho,method,nrep,seed):
    np.random.seed(seed);cap=budget//4
    values=np.empty(nrep);works=np.empty(nrep,dtype=np.int64);outers=np.empty(nrep,dtype=np.int64)
    for r in range(nrep):
        k=0;success=0;work=0
        while success<2:
            v,c=term(model,loss,cap,rho,method);k+=1;work+=c
            if np.random.random()<c/cap:success+=1
        sm=0.
        for j in range(k-1):
            v,c=term(model,loss,cap,rho,method);sm+=v;work+=c
        values[r]=sm/(k-1);works[r]=work;outers[r]=2*k-1
    return values,works,outers

def summarize(v,c,theta,eps,seed):
    rng=np.random.default_rng(seed);clipped=np.clip(v,0,1)
    ix=rng.integers(len(v),size=(2000,len(v)))
    out={}
    for name,values in [('raw',v),('clipped',clipped)]:
        error=values-theta
        out[name]=dict(rmse=float(np.sqrt(np.mean(error**2))),bias=float(error.mean()),
            variance=float(values.var(ddof=0)),miss_probability=float(np.mean(abs(error)>eps)),
            descriptive_rmse_interval=np.quantile(np.sqrt(np.mean(error[ix]**2,axis=1)),[.025,.975]).tolist())
    out.update(mean_work=float(c.mean()),work_quantiles={str(p):float(np.quantile(c,p)) for p in [.5,.9,.95,.99,1.]},
        work_total=int(c.sum()),clipped_fraction=float(np.mean(v!=clipped)),coverage=None,
        mean_work_interval=np.quantile(c[ix].mean(axis=1),[.025,.975]).tolist())
    return out

def lock():
    config=HERE/'PREREGISTRATION.json'
    if config.exists():raise RuntimeError('Already locked')
    specs=[('gha_published',.025,.1),('gha_rare',.005,.02),('fixed_gap',.01,.04),
        ('mixed_scales',.02,.04),('near_negative',.05,.1),('uniform_gaussian',.05,.1),('deterministic_endpoint',.02,.04)]
    d=dict(status='NUMERICAL',budgets=[4096,16384],replications=128,models=[dict(id=i,name=s[0],theta=s[1],rho=s[2],epsilon=max(.0025,s[1]/2)) for i,s in enumerate(specs)],
        methods=['gha_calibrated_single_level','direct_symmetric','direct_asymmetric'],
        seed_formula='202610270 + 10000*model + 100*budget_index + method',
        metrics='Raw and [0,1]-clipped RMS, bias, population empirical variance, miss probability; mean work/quantiles; wall seconds; no confidence procedure',
        exclusions='None. Failed cells retained; no rerun or tuning on this test.',
        selection='One candidate (asymmetric), fixed analytically before new data. Symmetric ablation and GHA comparator. No fitted allocation or training.',
        comparison='Matched observation oracle; calibrated expected budget bound. GHA Algorithm1 sampling component only, single base level; not published full MLMC driver.',
        observations='Each original real observation charged 1; fresh outer draws recorded as uncharged as inherited convention. Arithmetic/randomization free. No Bernoulli conversion for GHA.',
        uncertainty='2000-resample percentile bootstrap is descriptive only; no claimed heavy-tail or performance confidence certificate.',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    config.write_text(json.dumps(d,indent=2)+'\n');print('Locked',config)

def test():
    d=json.loads((HERE/'PREREGISTRATION.json').read_text())
    assert hashlib.sha256(Path(__file__).read_bytes()).hexdigest()==d['source_sha256']
    marker=HERE/'TEST_STARTED.json'
    if marker.exists():raise RuntimeError('Test already started; do not reuse held-out data')
    marker.write_text(json.dumps(dict(prereg_sha256=hashlib.sha256((HERE/'PREREGISTRATION.json').read_bytes()).hexdigest(),started=time.time()))+'\n')
    rows=[];raw={};start=time.perf_counter()
    for model in d['models']:
        theta=model['theta'];mid=model['id'];rho=model['rho']
        loss=float(.02*(ndtri(1-theta/2)**2-1)) if mid<=1 else 0.
        for bi,b in enumerate(d['budgets']):
            for mi,method in enumerate(d['methods']):
                seed=202610270+10000*mid+100*bi+mi;t=time.perf_counter()
                v,c,outer=replicates(mid,loss,b,rho,mi,d['replications'],seed)
                seconds=time.perf_counter()-t
                row=dict(model=model['name'],budget=b,method=method,seed=seed,theta=theta,rho=rho,epsilon=model['epsilon'],seconds=seconds,mean_outer_draws=float(outer.mean()),outer_total=int(outer.sum()),mean_work_if_outer_charged=float((outer+c).mean()),
                    **summarize(v,c,theta,model['epsilon'],seed+77))
                rows.append(row);key=f'{mid}_{b}_{mi}';raw[key+'_value']=v;raw[key+'_work']=c;raw[key+'_outer']=outer
                print(model['name'],b,method,'rmse',row['clipped']['rmse'],'work',row['mean_work'],flush=True)
                np.savez_compressed(HERE/'BENCHMARK_RAW.npz',**raw)
                (HERE/'BENCHMARK_RESULTS.json').write_text(json.dumps(dict(complete=False,rows=rows),indent=2)+'\n')
    (HERE/'BENCHMARK_RESULTS.json').write_text(json.dumps(dict(complete=True,rows=rows,seconds=time.perf_counter()-start,total_work=sum(r['work_total'] for r in rows),training_work=0,tuning_work=0,
        trivial=[dict(model=m['name'],zero_rmse=m['theta'],half_rmse=abs(.5-m['theta']),rarity_half_rmse=abs(m['rho']/2-m['theta'])) for m in d['models']]),indent=2)+'\n')

if __name__=='__main__':
    {'lock':lock,'test':test}[sys.argv[1]]()
