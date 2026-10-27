"""Frozen float64 nonlinear feedback experiment; no unrestricted minimax claim."""
from pathlib import Path
import hashlib,json,math,random,sys,time,csv
from fractions import Fraction as F
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'.runtime/python'))
import numpy as np

LAWS=[dict(name='two_scales',d=[1/32,1/4],mass=[1/8,7/8]),
      dict(name='four_scales',d=[1/128,1/32,1/8,1/4],mass=[1/64,3/64,3/16,3/4])]
MODES=['feedback','fresh','block4','block16']
BUDGETS=[64,256,1024]
RHOS=[1/4,1/16]
REPLICATES=32

def fill(mass,theta,reverse=False):
    q=np.zeros(len(mass));left=theta
    for i in (range(len(mass)-1,-1,-1) if reverse else range(len(mass))):
        take=min(left,mass[i]);q[i]=take/mass[i];left-=take
    assert abs(left)<1e-14
    return q

def radial(d,mass,theta):
    low,high=0.,max(d)**2
    for _ in range(80):
        mid=(low+high)/2
        if np.dot(mass,np.minimum(1.,mid/(d*d)))<theta:low=mid
        else:high=mid
    return np.minimum(1.,(low+high)/(2*d*d))

class Model:
    def __init__(self,law,rho):
        self.d=np.array(law['d']);self.mass=np.array(law['mass']);self.rho=rho
        rows=[np.zeros(len(self.d))]
        for theta in [rho/2,rho]:
            rows += [np.full(len(self.d),theta),fill(self.mass,theta),fill(self.mass,theta,True),radial(self.d,self.mass,theta)]
            for i,m in enumerate(self.mass):
                if theta<=m:
                    q=np.zeros(len(self.d));q[i]=theta/m;rows.append(q)
        unique=[]
        for row in rows:
            if not any(np.max(abs(row-old))<1e-14 for old in unique):unique.append(row)
        self.q=np.array(unique);self.target=self.q@self.mass
        self.cache={};self.pp=.5+self.d;self.pm=.5-self.d
        assert np.all(self.q>=0) and np.all(self.q<=1) and np.max(self.target)<=rho+1e-14

    def predictive(self,h,t):
        key=h,t
        if key not in self.cache:
            plus=h*np.log(self.pp)+t*np.log(self.pm)
            minus=h*np.log(self.pm)+t*np.log(self.pp)
            scale=max(float(np.max(plus)),float(np.max(minus)))
            plus=np.exp(plus-scale)*self.mass;minus=np.exp(minus-scale)*self.mass
            den=self.q@plus+(1-self.q)@minus
            num=self.q@(plus*self.pp)+(1-self.q)@(minus*self.pm)
            self.cache[key]=num/den
        return self.cache[key]

    def profiles(self):
        hard=fill(self.mass,self.rho);easy=fill(self.mass,self.rho,True)
        return dict(zero=np.zeros(len(self.d)),uniform=np.full(len(self.d),self.rho),
                    hard=hard,easy=easy,unseen_mixture=.6*(.6*hard+.4*easy))

class Reservoir:
    """Only flip(identity) is supplied to the policy; latent values stay here."""
    def __init__(self,d,mass,q,seed):
        self.d=d;self.mass=mass;self.q=q;self.seed=seed;self.coins={};self.work=0
    def flip(self,identity):
        if identity not in self.coins:
            latent=random.Random(self.seed+1000003*identity+12345)
            u=latent.random();i=0
            while u>=self.mass[i]:u-=self.mass[i];i+=1
            sign=latent.random()<self.q[i]
            p=.5+(1 if sign else -1)*self.d[i]
            tape=random.Random(self.seed+1000003*identity+67890)
            self.coins[identity]=(p,tape)
        p,tape=self.coins[identity];self.work+=1
        return int(tape.random()<p)

def estimate(model,flip,budget,mode):
    weights=np.full(len(model.q),1/len(model.q));hist=[]
    for step in range(budget):
        if mode=='feedback':
            # Equal local histories have equal action values; keep first identity.
            choices={}
            for i,key in enumerate(hist):choices.setdefault(key,i)
            choices[(0,0)]=len(hist)
            keys=list(choices);pred=np.array([model.predictive(*key) for key in keys])
            mean=float(weights@model.target);means=pred@weights
            cov=pred@(weights*model.target)-means*mean
            gains=cov*cov/(means*(1-means))
            index=int(np.argmax(gains));coin=choices[keys[index]];prob=pred[index]
        else:
            size=1 if mode=='fresh' else int(mode[5:])
            coin=step//size
            key=hist[coin] if coin<len(hist) else (0,0)
            prob=model.predictive(*key)
        if coin==len(hist):hist.append((0,0))
        bit=flip(coin);h,t=hist[coin];hist[coin]=(h+bit,t+1-bit)
        weights*=prob if bit else 1-prob
        den=float(weights.sum());assert den>0 and math.isfinite(den)
        weights/=den
    result=float(weights@model.target)
    assert -1e-14<=result<=model.rho+1e-14
    return result,max(h+t for h,t in hist),len(hist)

def identities():
    law=LAWS[0];m=Model(law,1/4);count=0
    for h in range(4):
        for t in range(4):
            got=m.predictive(h,t)
            for j,q in enumerate(m.q):
                den=F(0);num=F(0)
                for gap,mass,positive in zip(m.d,m.mass,q):
                    gap,mass,positive=map(F,[float(gap),float(mass),float(positive)])
                    for s,pr in [(1,positive),(-1,1-positive)]:
                        p=F(1,2)+s*gap;term=mass*pr*p**h*(1-p)**t
                        den+=term;num+=term*p
                assert abs(got[j]-float(num/den))<2e-15;count+=1
    w=np.full(len(m.q),1/len(m.q));p=m.predictive(1,0);bar=float(w@p)
    old=float(w@(m.target*m.target)-(w@m.target)**2)
    posterior=[]
    for bit in [0,1]:
        v=w*(p if bit else 1-p);pr=float(v.sum());v/=pr
        posterior.append(pr*float(v@(m.target*m.target)-(v@m.target)**2))
    formula=float(w@(p*m.target)-bar*(w@m.target))**2/(bar*(1-bar))
    assert abs(old-sum(posterior)-formula)<1e-16
    return dict(predictive_fraction_comparisons=count,variance_reduction_identity=True)

def lock():
    path=HERE/'EXPERIMENT_LOCK.json'
    if path.exists():raise RuntimeError('Already locked')
    checks=identities()
    spec=dict(laws=LAWS,rhos=RHOS,budgets=BUDGETS,replicates=REPLICATES,modes=MODES,
              seed_rule='2026102700+100000000*law_index+10000000*rho_index+100000*profile_index+replicate; same seed across policies and budgets',
              precision='IEEE754 float64 likelihoods/posteriors; Python random53-bit uniforms',
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              contract_sha256=hashlib.sha256((HERE/'CONTRACT.md').read_bytes()).hexdigest(),
              identity_checks=checks,numpy=np.__version__,python=sys.version,
              scope='Frozen exploratory heuristic evaluation, not uniform minimax or practical-superiority certificate')
    path.write_text(json.dumps(spec,indent=2)+'\n');print(json.dumps(checks))

def run():
    lockdata=json.loads((HERE/'EXPERIMENT_LOCK.json').read_text())
    assert lockdata['source_sha256']==hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    assert lockdata['contract_sha256']==hashlib.sha256((HERE/'CONTRACT.md').read_bytes()).hexdigest()
    path=HERE/'RAW.csv'
    if path.exists():raise RuntimeError('Do not overwrite evaluation')
    started=time.perf_counter();n=0
    with path.open('w',newline='') as file:
        fields=['law','rho','profile','budget','replicate','mode','theta','estimate','clipped','work','seconds','max_depth','coins']
        writer=csv.DictWriter(file,fieldnames=fields);writer.writeheader()
        for li,law in enumerate(LAWS):
            for ri,rho in enumerate(RHOS):
                model=Model(law,rho)
                for pi,(profile,q) in enumerate(model.profiles().items()):
                    theta=float(model.mass@q)
                    for budget in BUDGETS:
                        for rep in range(REPLICATES):
                            seed=2026102700+100000000*li+10000000*ri+100000*pi+rep
                            for mode in MODES:
                                reservoir=Reservoir(model.d,model.mass,q,seed)
                                start=time.perf_counter()
                                value,depth,coins=estimate(model,reservoir.flip,budget,mode)
                                elapsed=time.perf_counter()-start
                                assert reservoir.work==budget
                                writer.writerow(dict(law=law['name'],rho=rho,profile=profile,budget=budget,replicate=rep,mode=mode,theta=theta,estimate=value,clipped=min(1,max(0,value)),work=reservoir.work,seconds=elapsed,max_depth=depth,coins=coins));n+=1
                        file.flush()
                    print(law['name'],rho,profile,'rows',n,'seconds',round(time.perf_counter()-started,2),flush=True)
    (HERE/'EXPERIMENT_COMPLETE.json').write_text(json.dumps(dict(complete=True,rows=n,seconds=time.perf_counter()-started,lock_sha256=hashlib.sha256((HERE/'EXPERIMENT_LOCK.json').read_bytes()).hexdigest(),raw_sha256=hashlib.sha256(path.read_bytes()).hexdigest()),indent=2)+'\n')

if __name__=='__main__':{'lock':lock,'run':run}[sys.argv[1]]()
