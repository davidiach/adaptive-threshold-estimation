"""Independent labeled-tape recursion; checks the locked canonical-state DP."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import hashlib, json, time

HERE = Path(__file__).resolve().parent

def verify(case, maximum=5):
    # No imports from the production implementation; use the locked inputs.
    d, mass = [[F(x) for x in case[k]] for k in ('gaps', 'mass')]
    qs = [list(map(F,q)) for q in case['q']]
    targets = [sum(m*q for m,q in zip(mass,qs0)) for qs0 in qs]

    @lru_cache(None)
    def weights(tapes):
        ans=[]
        for q in qs:
            value=F(1,len(qs))
            for tape in tapes:
                local=F(0)
                for gap,m,positive in zip(d,mass,q):
                    for sign,prob in [(1,positive),(-1,1-positive)]:
                        term=m*prob
                        p=F(1,2)+sign*gap
                        for bit in tape: term*=p if bit else 1-p
                        local+=term
                value*=local
            ans.append(value)
        return tuple(ans)

    @lru_cache(None)
    def recurse(tapes,remaining):
        w=weights(tapes); den=sum(w)
        if not remaining:
            first=sum(p*t for p,t in zip(w,targets))/den
            second=sum(p*t*t for p,t in zip(w,targets))/den
            return second-first*first
        candidates=[]
        for action in range(len(tapes)+1):
            children=[]
            for bit in (0,1):
                child=list(tapes)
                if action==len(tapes):child.append((bit,))
                else:child[action]=child[action]+(bit,)
                child=tuple(child)
                probability=sum(weights(child))/den
                children.append((probability,recurse(child,remaining-1)))
            assert sum(p for p,r in children)==1
            candidates.append(sum(p*r for p,r in children))
        return min(candidates)
    return [recurse((),n) for n in range(1,maximum+1)]

def main():
    start=time.perf_counter()
    spec=json.loads((HERE/'FINITE_LOCK.json').read_text())
    results=json.loads((HERE/'FINITE_RESULTS.json').read_text())
    checks=[]
    for case in spec['cases']:
        vals=verify(case)
        for n,value in enumerate(vals,1):
            expected=next(r for r in results['rows'] if r['case']==case['name'] and r['B']==n)
            assert value==F(expected['risks']['adaptive'])
            checks.append(dict(case=case['name'],horizon=n,risk=str(value),equal=True))
    out=dict(valid=True,arithmetic='Python exact Fraction; no Monte Carlo',checks=checks,
             scope='Independent labeled ordered-bit histories, horizons1..5; the production DP reaches8',
             script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             result_sha256=hashlib.sha256((HERE/'FINITE_RESULTS.json').read_bytes()).hexdigest(),
             seconds=time.perf_counter()-start)
    target=HERE/'FINITE_VERIFY.json'
    if target.exists():raise RuntimeError('Do not overwrite verification record')
    target.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(valid=True,exact_comparisons=len(checks),seconds=out['seconds'])))

if __name__=='__main__':main()
