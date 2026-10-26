"""Giles--Haji-Ali Section 3 model: adaptive MLMC vs v4, independent tuning/test.
All inner pilot draws counted. MLMC allocation moments are learned OFFLINE;
training expense reported separately, not hidden in per-estimate work.
Only final outputs clipped. Tuned variants are experimental, not new guarantees.
"""
from __future__ import annotations
import argparse,json,math,time
from pathlib import Path
import numpy as np
from scipy.special import ndtri
from numba import njit
ROOT=Path(__file__).resolve().parents[1];RES=ROOT/'results';RES.mkdir(exist_ok=True)
TAU=.02;THETA=.025;LOSS=float(TAU*(ndtri(1-THETA/2)**2-1))
@njit(cache=True)
def seed_rng(s):np.random.seed(s)
@njit(cache=True)
def real_x(y):
 u=np.random.normal();z=np.random.normal()
 return TAU*(y*y-u*u)+2*math.sqrt(TAU*(1-TAU))*y*z-LOSS
@njit(cache=True)
def coin_x(y):
 x=real_x(y);v=np.random.normal()
 return int(x+TAU*(v*v-1)>0)
@njit(cache=True)
def adaptive_n(y,level,n0,C,r):
 n=n0*(2**level);cap=n0*(4**level);cost=0
 while True:
  if 2*n>=cap:return cap,cost
  sm=0.;ss=0.
  for i in range(n):
   x=real_x(y);sm+=x;ss+=x*x
  cost+=n;d=abs(sm/n);sig=math.sqrt(max(0.,ss/n-(sm/n)**2))
  if sig==0.:target=0. if d>0 else float(cap)
  elif d==0.:target=float(cap)
  else:target=cap*(math.sqrt(n0)*(2**level)*d/(C*sig))**(-r)
  if n>=target:return n,cost
  n*=2
@njit(cache=True)
def gha_term(level,base,n0,C,r):
 y=np.random.normal();nf,cf=adaptive_n(y,level,n0,C,r)
 if base:
  total=0.
  for k in range(nf):total+=real_x(y)
  return (1.0 if total>0 else 0.0),cf+nf
 nc,cc=adaptive_n(y,level-1,n0,C,r)
 nmax=max(nf,nc);sf=0.;sc=0.;vf=0.;vc=0.
 for k in range(nmax):
  x=real_x(y);sf+=x;sc+=x
  if (k+1)%nf==0:vf+=(1.0 if sf>0 else 0.0);sf=0.
  if (k+1)%nc==0:vc+=(1.0 if sc>0 else 0.0);sc=0.
 return vf/(nmax//nf)-vc/(nmax//nc),cf+cc+nmax
@njit(cache=True)
def term_samples(level,base,n0,C,r,reps):
 v=np.empty(reps);c=np.empty(reps)
 for i in range(reps):v[i],c[i]=gha_term(level,base,n0,C,r)
 return v,c
@njit(cache=True)
def bern_pair(j,start,ratio,threshold):
 cap=start*(ratio**j);other=0 if j==0 else cap//ratio
 z=-1;zc=0 if j==0 else -1;heads=0;previous=0;n=1;y=np.random.normal()
 while True:
  for k in range(previous,n):heads+=coin_x(y)
  x=heads/n-.5
  if z<0:
   if n>=cap:z=int(x>0)
   elif abs(x)>threshold*math.sqrt((1+math.log(cap/n))/n):z=int(x>0)
  if zc<0:
   if n>=other:zc=int(x>0)
   elif abs(x)>threshold*math.sqrt((1+math.log(other/n))/n):zc=int(x>0)
  if z>=0 and zc>=0:return z-zc,n
  previous=n;n*=2
@njit(cache=True)
def bern_term(L,start,ratio,threshold):
 r=ratio**(-.5);p=1-r;j=int(math.floor(math.log(1-np.random.random())/math.log(r)))
 if j>L:return 0.,0
 v,w=bern_pair(j,start,ratio,threshold)
 return v/(p*r**j),w
@njit(cache=True)
def bern_estimate(B,start,ratio,threshold):
 if B<4*start:return .5,0
 L=0
 while start*(ratio**(L+1))<=B/4:L+=1
 cap=start*(ratio**L);K=0;successes=0;work=0
 while successes<2:
  z,c=bern_term(L,start,ratio,threshold);K+=1;work+=c
  if np.random.random()<c/cap:successes+=1
 total=0.
 for i in range(K-1):
  z,c=bern_term(L,start,ratio,threshold);total+=z;work+=c
 return total/(K-1),work
@njit(cache=True)
def bern_replicates(B,start,ratio,threshold,reps):
 v=np.empty(reps);c=np.empty(reps)
 for i in range(reps):v[i],c[i]=bern_estimate(B,start,ratio,threshold)
 return v,c
@njit(cache=True)
def gha_replicates(levels,counts,n0,C,r,reps):
 v=np.empty(reps);c=np.empty(reps)
 for i in range(reps):
  estimate=0.;work=0
  for li in range(len(levels)):
   total=0.
   for j in range(counts[li]):
    z,w=gha_term(levels[li],li==0,n0,C,r);total+=z;work+=w
   estimate+=total/counts[li]
  v[i]=estimate;c[i]=work
 return v,c

def summarize(v,c):
 v=np.asarray(v);c=np.asarray(c);vc=np.clip(v,0,1);sq=(vc-THETA)**2;rmse=float(np.sqrt(sq.mean()))
 return dict(n=len(v),rmse=rmse,rmse_se_delta=float(sq.std(ddof=1)/np.sqrt(len(v))/(2*rmse)),rmse_raw=float(np.sqrt(np.mean((v-THETA)**2))),mean=float(vc.mean()),bias=float(vc.mean()-THETA),mean_work=float(c.mean()),work_se=float(c.std(ddof=1)/np.sqrt(len(c))),work_p95=float(np.quantile(c,.95)),work_max=float(c.max()),clipped_fraction=float(np.mean((v<0)|(v>1))))

def allocate(B,tr,key):
 n0=tr[key]['config']['n0'];L=max(0,int(math.floor(math.log(max(1,B/(4*n0)),4))));L=min(L,5);opts=[]
 for base in range(L+1):
  vv=[];cc=[]
  for l in range(base,L+1):
   cell=tr[key]['levels'][str(l)]['base' if l==base else 'delta'];vv.append(max(cell['variance'],1/(4*cell['n'])));cc.append(cell['work'])
  v=np.array(vv);c=np.array(cc);S=np.sqrt(v*c).sum();counts=np.maximum(1,np.floor(B/S*np.sqrt(v/c))).astype(np.int64)
  opts.append((float(np.sum(v/counts)),base,counts,float(c@counts)))
 _,base,counts,expected=min(opts,key=lambda o:o[0])
 return np.arange(base,L+1,dtype=np.int64),counts,expected
GHA_CONFIGS=[dict(n0=32,C=3.,r=1.5),dict(n0=8,C=3.,r=1.5),dict(n0=32,C=1.,r=1.5),dict(n0=8,C=1.,r=1.5)]
BERN_CONFIGS=[dict(start=s,ratio=q,threshold=t) for s in [1,16] for q in [2,4] for t in [.35,.65,1.]]
BUDGETS=[1024,4096,16384,65536]
def train(n=4000):
 t0=time.time();tr={};tw=0.
 for i,conf in enumerate(GHA_CONFIGS):
  key=f'gha_{i}';tr[key]={'config':conf,'levels':{}};seed_rng(11000+i)
  for l in range(6):
   tr[key]['levels'][str(l)]={}
   for base in ([True,False] if l else [True]):
    v,c=term_samples(l,base,**conf,reps=n);tr[key]['levels'][str(l)]['base' if base else 'delta']=dict(n=n,mean=float(v.mean()),variance=float(v.var(ddof=1)),work=float(c.mean()),total_work=float(c.sum()));tw+=c.sum()
  print('trained',key,conf,flush=True)
 out=dict(model=dict(tau=TAU,loss=LOSS,theta=THETA),training=tr,total_work=tw,seconds=time.time()-t0);(RES/'training.json').write_text(json.dumps(out,indent=2));return out

def tune(n=100):
 tr=json.loads((RES/'training.json').read_text())['training'];rows=[];t0=time.time()
 for bi,B in enumerate(BUDGETS):
  for i,conf in enumerate(GHA_CONFIGS):
   seed_rng(21000+bi*100+i);lev,cnt,expected=allocate(B,tr,f'gha_{i}');v,c=gha_replicates(lev,cnt,**conf,reps=n);rows.append(dict(method='gha',index=i,budget=B,config=conf,levels=lev.tolist(),counts=cnt.tolist(),planned_work=expected,**summarize(v,c)))
  for i,conf in enumerate(BERN_CONFIGS):
   seed_rng(31000+bi*100+i);v,c=bern_replicates(B,**conf,reps=n);rows.append(dict(method='bernoulli',index=i,budget=B,config=conf,**summarize(v,c)))
  print('tuned budget',B,flush=True)
 out=dict(rows=rows,total_work=sum(x['mean_work']*n for x in rows),seconds=time.time()-t0);(RES/'tuning.json').write_text(json.dumps(out,indent=2));return out

def test(n=500):
 tr=json.loads((RES/'training.json').read_text())['training'];tu=json.loads((RES/'tuning.json').read_text())['rows'];rows=[];raw={};t0=time.time()
 for bi,B in enumerate(BUDGETS):
  bg=min((x for x in tu if x['budget']==B and x['method']=='gha'),key=lambda x:x['rmse']);bb=min((x for x in tu if x['budget']==B and x['method']=='bernoulli'),key=lambda x:x['rmse'])
  specs=[('gha_reference',GHA_CONFIGS[0],0),('gha_tuned',bg['config'],bg['index']),('v4_reference',dict(start=1,ratio=2,threshold=1.),-1),('v4_tuned',bb['config'],bb['index'])]
  for mi,(name,conf,index) in enumerate(specs):
   seed_rng(41000+bi*100+mi)
   if name.startswith('gha'):
    lev,cnt,expected=allocate(B,tr,f'gha_{index}');v,c=gha_replicates(lev,cnt,**conf,reps=n);extra=dict(levels=lev.tolist(),counts=cnt.tolist(),planned_work=expected)
   else:v,c=bern_replicates(B,**conf,reps=n);extra={}
   raw[f'{name}_{B}_value']=v;raw[f'{name}_{B}_work']=c;rows.append(dict(method=name,budget=B,config=conf,**extra,**summarize(v,c)));print(name,B,'rmse',rows[-1]['rmse'],'work',rows[-1]['mean_work'],flush=True)
 out=dict(rows=rows,total_work=sum(x['mean_work']*n for x in rows),seconds=time.time()-t0,baseline_zero_rmse=THETA,baseline_half_rmse=.5-THETA,replications=n);(RES/'test.json').write_text(json.dumps(out,indent=2));np.savez_compressed(RES/'test_raw.npz',**raw);return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['train','tune','test','all']);p.add_argument('--n',type=int,default=None);a=p.parse_args()
 if a.stage in ['train','all']:train(a.n or 4000)
 if a.stage in ['tune','all']:tune(a.n or 100)
 if a.stage in ['test','all']:test(a.n or 500)
