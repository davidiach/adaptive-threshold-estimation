"""Floating-point exploration of Q/K; not a proof or certificate."""
import json, math, sys, time
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent))
from runtime_output import output_directory
out,_=output_directory(__doc__)
rng=np.random.default_rng(731924)
cache={}
maxcase=None;maxratio=0.; checked=0;subset_count=0
start=time.perf_counter()
for trial in range(20000):
 n=int(rng.integers(2,9))
 if n not in cache:
  cache[n]=((np.arange(1<<n)[:,None] >> np.arange(n))&1).astype(float)
 masks=cache[n]
 bands=rng.integers(0,15,n)
 ds=2.**(-(bands+2))*(1+rng.random(n))
 logits=rng.uniform(-12,0,n); ws=np.exp(logits);ws/=ws.sum()
 order=np.argsort(ds);ds=ds[order];ws=ws[order];bands=bands[order]
 rho=float(10**rng.uniform(-6,math.log10(.25)))
 h=float(10**rng.uniform(-9,-.2))
 costs=ws/(ds*ds)
 groups=np.zeros((n,int(bands.max())+1))
 groups[np.arange(n),bands]=costs
 av=masks@groups;A=av.sum(axis=1)
 with np.errstate(divide='ignore',invalid='ignore'):
  logs=np.where(av>0,np.log(np.divide(A[:,None],av,out=np.ones_like(av),where=av>0)),0)
  G=A+(av*logs).sum(axis=1)
 ordinary=ws*np.minimum(1,h/ds)
 objectives=np.sqrt(np.maximum(0,rho*G))*h+(1-masks)@ordinary
 K=min(rho,float(objectives.min()))
 left=rho;core=np.ones(n)
 for i in range(n):
  removed=min(left,ws[i]);core[i]=1-removed/ws[i];left-=removed
 ac=core@groups;AC=ac.sum();GC=AC+sum(a*np.log(AC/a) for a in ac if a>0)
 Q=min(rho,float(h*np.sqrt(rho*GC)+(1-core)@ordinary))
 ratio=Q/K
 if ratio>maxratio:
  maxratio=ratio
  maxcase={'trial':trial,'gaps':ds.tolist(),'masses':ws.tolist(),'rho':rho,'h':h,'K_float':K,'Q_float':Q,'Q_over_K_float':ratio,'best_mask':masks[objectives.argmin()].astype(int).tolist()}
 if ratio>1.6+1e-10: raise AssertionError(maxcase)
 checked+=1;subset_count+=len(masks)
result={'scope':'floating_point_exploration_not_proof_or_certificate','seed':731924,'laws_checked':checked,'subsets_evaluated':subset_count,'elapsed_seconds':time.perf_counter()-start,'largest_ratio':maxcase}
(out/'float_exploration.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
print(f'wrote {out/"float_exploration.json"}; timing differs between runs, so it is not compared')
