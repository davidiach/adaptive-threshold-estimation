"""Large-budget extrapolation, constants locked by the ORIGINAL tuning set.
Forces GHA's starting level <=4 so the extension really uses multiple levels.
Does not retune against its test outputs. Separate seeds and raw records.
"""
import json,time
import numpy as np
from benchmark import RES,GHA_CONFIGS,term_samples,seed_rng,gha_replicates,bern_replicates,summarize

def extension(n=150):
    t0=time.time(); inp=json.loads((RES/'training.json').read_text());tr=inp['training'];added=0.
    tuning=json.loads((RES/'tuning.json').read_text())['rows']
    bg=min((x for x in tuning if x['budget']==65536 and x['method']=='gha'),key=lambda x:x['rmse'])
    bb=min((x for x in tuning if x['budget']==65536 and x['method']=='bernoulli'),key=lambda x:x['rmse'])
    for idx in set([0,bg['index']]):
        conf=GHA_CONFIGS[idx];seed_rng(51000+idx)
        for level in range(6,7):
            tr[f'gha_{idx}']['levels'][str(level)]={}
            for base in [True,False]:
                v,c=term_samples(level,base,**conf,reps=4000)
                tr[f'gha_{idx}']['levels'][str(level)]['base' if base else 'delta']=dict(n=4000,mean=float(v.mean()),variance=float(v.var(ddof=1)),work=float(c.mean()),total_work=float(c.sum()));added+=c.sum()
    rows=[];raw={}
    (RES/'extension_training.json').write_text(json.dumps(dict(training=tr,total_work=added),indent=2))
    for bi,B in enumerate([262144]):
        specs=[('gha_reference',GHA_CONFIGS[0],0),('gha_tuned',bg['config'],bg['index']),('v4_reference',dict(start=1,ratio=2,threshold=1.),-1),('v4_tuned',bb['config'],bb['index'])]
        for mi,(name,conf,idx) in enumerate(specs):
            seed_rng(61000+bi*100+mi)
            if name.startswith('gha'):
                n0=conf['n0'];L=int(np.floor(np.log(B/(4*n0))/np.log(4)));base=min(4,L);vv=[];cc=[]
                for l in range(base,L+1):
                    x=tr[f'gha_{idx}']['levels'][str(l)]['base' if l==base else 'delta'];vv.append(max(x['variance'],1/(4*x['n'])));cc.append(x['work'])
                vv=np.array(vv);cc=np.array(cc);S=np.sqrt(vv*cc).sum();cnt=np.maximum(1,np.floor(B/S*np.sqrt(vv/cc))).astype(np.int64);lev=np.arange(base,L+1,dtype=np.int64)
                v,c=gha_replicates(lev,cnt,**conf,reps=n);extra=dict(levels=lev.tolist(),counts=cnt.tolist(),planned_work=float(cc@cnt))
            else:v,c=bern_replicates(B,**conf,reps=n);extra={}
            rows.append(dict(method=name,budget=B,config=conf,**extra,**summarize(v,c)));raw[f'{name}_{B}_value']=v;raw[f'{name}_{B}_work']=c
            print(name,B,rows[-1]['rmse'],rows[-1]['mean_work'],flush=True)
            (RES/'extension_partial.json').write_text(json.dumps(rows,indent=2));np.savez_compressed(RES/'extension_raw.npz',**raw)
    out=dict(rows=rows,additional_training_work=added,total_work=sum(x['mean_work']*n for x in rows),seconds=time.time()-t0,replications=n,configuration_selection='locked from original 65536-budget tuning only',training=tr)
    (RES/'extension.json').write_text(json.dumps(out,indent=2));np.savez_compressed(RES/'extension_raw.npz',**raw)
if __name__=='__main__':extension()
