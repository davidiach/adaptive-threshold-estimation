"""Exact rational adaptive finite-horizon Bayes diagnostics; no minimax claim."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent

def canonical(coins):return tuple(sorted(coins))

class Experiment:
    def __init__(self,gaps,masses,rho=F(1,8)):
        self.d=tuple(gaps);self.mass=tuple(masses);self.rho=rho
        qs=[tuple(F(0) for _ in gaps)]
        for i,m in enumerate(masses):
            for theta in [rho/2,rho]:
                if theta<=m:
                    q=[F(0) for _ in gaps];q[i]=theta/m;qs.append(tuple(q))
        qs.append(tuple(rho for _ in gaps));self.q=tuple(dict.fromkeys(qs));self.prior=F(1,len(self.q))
        self.theta=tuple(sum(m*x for m,x in zip(masses,q)) for q in self.q)
        assert all(0<=t<=rho for t in self.theta)

    @lru_cache(None)
    def local(self,h,t,k):
        return sum(m*(q*(F(1,2)+d)**h*(F(1,2)-d)**t+(1-q)*(F(1,2)-d)**h*(F(1,2)+d)**t) for d,m,q in zip(self.d,self.mass,self.q[k]))

    @lru_cache(None)
    def likelihood(self,s,k):
        value=F(1)
        for h,t in s:value*=self.local(h,t,k)
        return value

    @lru_cache(None)
    def evidence(self,s):return sum(self.prior*self.likelihood(s,k) for k in range(len(self.q)))

    @lru_cache(None)
    def estimate(self,s):
        den=self.evidence(s);assert den>0
        return sum(self.prior*self.likelihood(s,k)*self.theta[k] for k in range(len(self.q)))/den

    @lru_cache(None)
    def terminal(self,s):
        est=self.estimate(s)
        return sum(self.prior*self.likelihood(s,k)*(est-self.theta[k])**2 for k in range(len(self.q)))/self.evidence(s)

    def next(self,s,action,bit):
        coins=list(s)
        if action==len(s):coins.append((bit,1-bit))
        else:
            h,t=coins[action];coins[action]=(h+bit,t+1-bit)
        return canonical(coins)

    def actions(self,s):
        return [i for i in range(len(s)) if i==0 or s[i]!=s[i-1]]+[len(s)]

    def branch(self,s,action,bit):
        nxt=self.next(s,action,bit)
        return nxt,self.evidence(nxt)/self.evidence(s)

    @lru_cache(None)
    def solve(self,s,remaining,mode):
        if remaining==0:return self.terminal(s),-1
        actions=self.actions(s) if mode=='adaptive' else [len(s)] if mode=='fresh' else [0]
        options=[]
        for action in actions:
            children=[self.branch(s,action,bit) for bit in [0,1]]
            assert sum(p for nxt,p in children)==1
            value=sum(p*self.solve(nxt,remaining-1,mode)[0] for nxt,p in children)
            assert value<=self.terminal(s)
            options.append((value,action))
        return min(options)

    @lru_cache(None)
    def conditional_risks(self,s,remaining,mode):
        if remaining==0:
            est=self.estimate(s);return tuple((est-t)**2 for t in self.theta)
        action=self.solve(s,remaining,mode)[1]
        children=[self.next(s,action,bit) for bit in [0,1]]
        risks=[self.conditional_risks(nxt,remaining-1,mode) for nxt in children]
        out=[]
        for k in range(len(self.q)):
            base=self.likelihood(s,k)
            out.append(sum(self.likelihood(nxt,k)*r[k] for nxt,r in zip(children,risks))/base if base else F(0))
        return tuple(out)

def cases():
    return [('two_scales',Experiment([F(1,32),F(1,4)],[F(1,8),F(7,8)])),
            ('three_scales',Experiment([F(1,32),F(1,8),F(1,2)],[F(1,16),F(3,16),F(3,4)]))]

def lock():
    path=HERE/'FINITE_LOCK.json'
    if path.exists():raise RuntimeError('Already locked')
    out=dict(scope='exact finite-prior Bayes risk at deterministic horizons1..8; not expected-budget minimax',
        contract_sha256=hashlib.sha256((HERE/'CONTRACT.md').read_bytes()).hexdigest(),
        implementation_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        cases=[dict(name=name,gaps=list(map(str,e.d)),mass=list(map(str,e.mass)),rho=str(e.rho),q=[list(map(str,q)) for q in e.q],prior=str(e.prior)) for name,e in cases()],horizons=list(range(1,9)),seed=None)
    path.write_text(json.dumps(out,indent=2)+'\n');print('Locked finite diagnostic')

def run():
    spec=json.loads((HERE/'FINITE_LOCK.json').read_text())
    assert spec['implementation_sha256']==hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    assert spec['contract_sha256']==hashlib.sha256((HERE/'CONTRACT.md').read_bytes()).hexdigest()
    path=HERE/'FINITE_RESULTS.json'
    if path.exists():raise RuntimeError('Do not overwrite completed finite diagnostic')
    start=time.perf_counter();rows=[]
    for name,e in cases():
        previous={m:None for m in ['adaptive','fresh','single']}
        for B in spec['horizons']:
            row=dict(case=name,B=B,risks={},conditional_risks={})
            for mode in ['adaptive','fresh','single']:
                val=e.solve((),B,mode)[0];risk=e.conditional_risks((),B,mode)
                assert sum(e.prior*r for r in risk)==val
                if previous[mode] is not None:assert val<=previous[mode]
                previous[mode]=val;row['risks'][mode]=str(val);row['conditional_risks'][mode]=list(map(str,risk))
            assert F(row['risks']['adaptive'])<=min(F(row['risks']['fresh']),F(row['risks']['single']))
            row['display_squared_risks']={m:float(F(r)) for m,r in row['risks'].items()}
            rows.append(row);print(name,B,row['display_squared_risks'],flush=True)
        # Enough history to show the actual observable action rule, with no D input.
        policy=[]
        def visit(s,remaining):
            if not remaining:return
            action=e.solve(s,remaining,'adaptive')[1]
            if (s,remaining) in seen:return
            seen.add((s,remaining));policy.append(dict(coins=s,remaining=remaining,action=('fresh' if action==len(s) else action)))
            for bit in [0,1]:visit(e.next(s,action,bit),remaining-1)
        seen=set();visit((),8)
        (HERE/(name+'_policy.json')).write_text(json.dumps(policy,indent=2)+'\n')
    out=dict(complete=True,status='NUMERICAL: exact rational finite-horizon dynamic program',
        scope=spec['scope'],rows=rows,seconds=time.perf_counter()-start,
        checks='probability sums, posterior-variance monotonicity, prior-average conditional risk identity; exact Fraction arithmetic',
        lock_sha256=hashlib.sha256((HERE/'FINITE_LOCK.json').read_bytes()).hexdigest())
    path.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':{'lock':lock,'run':run}[sys.argv[1]]()
