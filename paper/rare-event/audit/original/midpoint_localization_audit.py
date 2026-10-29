"""Independent adversarial checks of manuscript Appendices C.2 and C.6.

Standard library only. Coin probabilities, work, and seed marginalizations
use exact Fractions. Hellinger bounds use certified rational sqrt intervals.
No manuscript code is imported. These finite checks do not prove the general
theorems or their unbounded-stopping extension.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, isqrt
import json
import random


TYPES = [
    [(F(1,4), F(1,2), F(1,8), F(3,8)),
     (F(3,4), F(1,4), F(1,32), F(3,16))],
    [(F(1,2), F(1,8), F(1,16), F(1,4)),
     (F(1,2), F(1,2), F(1,32), F(1,8))],
    [(F(3,10), F(3,8), F(0), F(3,10)),
     (F(7,10), F(1,16), F(1,10), F(1,5))],
]


@lru_cache(None)
def kernel(typ, state, n, k):
    ans = F(0)
    for mass,d,ql,qh in TYPES[typ]:
        q = {'lo':ql, 'hi':qh, 'mid':(ql+qh)/2, 'null':F(0)}[state]
        pm, pp = F(1,2)-d, F(1,2)+d
        ans += mass*((1-q)*pm**k*(1-pm)**(n-k)+q*pp**k*(1-pp)**(n-k))
    return ans


def wordprob(typ, state, word):
    return kernel(typ, state, len(word), sum(word))


@lru_cache(None)
def sqrt_interval(q, bits=100):
    scale = 1 << bits
    root = isqrt(q.numerator*scale*scale//q.denominator)
    lo = F(root,scale)
    hi = lo if lo*lo == q else F(root+1,scale)
    assert lo*lo <= q <= hi*hi
    return lo,hi


def hellinger_interval(p,q):
    assert sum(p)==sum(q)==1
    if p == q:
        return F(0),F(0)
    roots = [sqrt_interval(a*b) for a,b in zip(p,q)]
    return max(F(0),1-sum(x[1] for x in roots)), 1-sum(x[0] for x in roots)


def certified_local_ratio(typ, cap, workref):
    # Bellman maximization over all capped single-unit stopping policies.
    # Rewards are upper enclosures of m_s-sqrt(p_minus,s p_plus,s).
    rewards = {}
    for n in range(cap+1):
        for k in range(n+1):
            lo,hi = sqrt_interval(kernel(typ,'lo',n,k)*kernel(typ,'hi',n,k))
            rewards[n,k] = kernel(typ,'mid',n,k)-lo
    def surplus(price):
        vals = {}
        for n in range(cap,0,-1):
            for k in range(n+1):
                vals[n,k] = rewards[n,k]
                if n<cap:
                    vals[n,k] = max(vals[n,k], vals[n+1,k]+vals[n+1,k+1]
                                   -price*kernel(typ,workref,n,k))
        return vals[1,0]+vals[1,1]-price
    lower,upper=F(0),F(2)
    assert surplus(upper)<=0
    for _ in range(42):
        middle=(lower+upper)/2
        if surplus(middle)<=0:
            upper=middle
        else:
            lower=middle
    assert surplus(upper)<=0
    return upper


def make_tree(seed, cap=7, maxunits=3, ntypes=3):
    rng=random.Random(seed)
    actions={}
    leaves=[]
    def visit(bits,types,words):
        depth=len(bits)
        stop = depth==cap or (depth>=3 and rng.randrange(5)==0)
        if stop:
            actions[bits]=None
            leaves.append((bits,types,words))
            return
        if depth==0:
            idx=0
            typ=rng.randrange(ntypes)
        elif depth==1:
            idx=1
            # Type chosen from the first unit's observed result.
            typ=(types[0]+bits[0]+1)%ntypes
        elif depth==2:
            idx,typ=0,types[0]  # Revisit the first unit after opening the second.
        elif len(types)<maxunits and rng.randrange(3)==0:
            idx=len(types)
            typ=(sum(bits)+rng.randrange(ntypes))%ntypes
        else:
            idx=rng.randrange(len(types))
            typ=types[idx]
        actions[bits]=(idx,typ)
        if idx==len(types):
            types=types+(typ,)
            words=words+((),)
        for x in (0,1):
            updated=list(words)
            updated[idx]=updated[idx]+(x,)
            visit(bits+(x,),types,tuple(updated))
    visit((),(),())
    return actions,leaves


def leaf_probability(leaf, assignment):
    _,types,words=leaf
    out=F(1)
    for i,(typ,word) in enumerate(zip(types,words)):
        out*=wordprob(typ,assignment(i),word)
    return out


def finite_tree_checks(trials=300, cap=7):
    km=max(certified_local_ratio(i,cap,'mid') for i in range(len(TYPES)))
    kn=max(certified_local_ratio(i,cap,'null') for i in range(len(TYPES)))
    leafcount=0
    largest=F(0)
    maxnull=F(0)
    for seed in range(20261100,20261100+trials):
        actions,leaves=make_tree(seed,cap)
        leafcount+=len(leaves)
        pl=[leaf_probability(z,lambda i:'lo') for z in leaves]
        ph=[leaf_probability(z,lambda i:'hi') for z in leaves]
        pm=[leaf_probability(z,lambda i:'mid') for z in leaves]
        assert sum(pl)==sum(ph)==sum(pm)==1
        hm=hellinger_interval(pl,ph)
        work=sum(p*len(z[0]) for p,z in zip(pm,leaves))
        localwork=F(0)
        hybridlower=F(0)
        for slot in range(3):
            hp=[];hq=[];null=[]
            for z in leaves:
                hp.append(leaf_probability(z,lambda i:'lo' if i==slot else 'mid'))
                hq.append(leaf_probability(z,lambda i:'hi' if i==slot else 'mid'))
                null.append(leaf_probability(z,lambda i:'null' if i==slot else 'mid'))
            assert sum(hp)==sum(hq)==sum(null)==1
            hl,hu=hellinger_interval(hp,hq)
            hybridlower+=hl
            counts=[len(z[2][slot]) if slot<len(z[2]) else 0 for z in leaves]
            wm=sum(p*n for p,n in zip(pm,counts))
            w0=sum(p*n for p,n in zip(null,counts))
            assert w0<=2*wm
            assert hu<=km*wm or hu==wm==0
            assert hu<=kn*w0 or hu==w0==0
            localwork+=wm
            if wm:
                maxnull=max(maxnull,w0/wm)
        assert localwork==work
        # Strict slack here permits rational sqrt enclosures to certify the inequality.
        assert hm[1]<=hybridlower
        assert hm[1]<=km*work
        assert hm[1]<=2*kn*work
        largest=max(largest,hm[1]/(km*work))
    return {'policies':trials,'cap':cap,'types':len(TYPES),'maximum_units':3,
            'terminal_leaves':leafcount,'certified_local_midpoint_ratio':str(km),
            'certified_local_null_ratio':str(kn),
            'largest_population_h_over_midpoint_bound':float(largest),
            'largest_local_null_work_over_midpoint_work':float(maxnull),
            'arithmetic':'exact rational probabilities; certified rational square-root enclosures',
            'all_checks_passed':True}


def seed_realization_checks(trials=4,cap=5):
    # Only two units and two types, allowing complete enumeration of the auxiliary
    # seed: one full midpoint tape for each possible type of the other unit.
    tape_list=list(product((0,1),repeat=cap))
    seeds=list(product(tape_list,repeat=2))
    seed_mass=[wordprob(0,'mid',s[0])*wordprob(1,'mid',s[1]) for s in seeds]
    assert sum(seed_mass)==1
    conditionalbranches=0
    for policyseed in range(20262000,20262000+trials):
        actions,leaves=make_tree(policyseed,cap,maxunits=2,ntypes=2)
        bybits={z[0]:z for z in leaves}
        for target in (0,1):
            coefficients={bits:F(0) for bits in bybits}
            work=F(0)
            for tapes,mass in zip(seeds,seed_mass):
                def run(bits,types,words):
                    action=actions[bits]
                    if action is None:
                        yield bits,types,words
                        return
                    idx,typ=action
                    if idx==len(types):
                        types=types+(typ,)
                        words=words+((),)
                    outcomes=(0,1) if idx==target else (tapes[typ][len(words[idx])],)
                    for x in outcomes:
                        updated=list(words)
                        updated[idx]=updated[idx]+(x,)
                        yield from run(bits+(x,),types,tuple(updated))
                pminus=pplus=pmid=F(0)
                for bits,types,words in run((),(),()):
                    conditionalbranches+=1
                    typ,word=types[target],words[target]
                    pminus+=wordprob(typ,'lo',word)
                    pplus+=wordprob(typ,'hi',word)
                    pmid+=wordprob(typ,'mid',word)
                    work+=mass*wordprob(typ,'mid',word)*len(word)
                    coefficients[bits]+=mass
                assert pminus==pplus==pmid==1
            expectedwork=F(0)
            for bits,coefficient in coefficients.items():
                z=bybits[bits]
                _,types,words=z
                other=1-target
                assert coefficient==wordprob(types[other],'mid',words[other])
                expectedwork+=leaf_probability(z,lambda i:'mid')*len(words[target])
            assert work==expectedwork
    return {'policies':trials,'targets_per_policy':2,'cap':cap,
            'independent_seeds_enumerated_per_target':len(seeds),
            'conditional_terminal_branches':conditionalbranches,
            'result':'Exact seed marginalization equals each hybrid leaf kernel; local work equals its slot work.',
            'all_checks_passed':True}


def endpoint_work_counterexample():
    # Known perfect-label magnitudes, all priors admissible for rho=1/4.
    n,k,extra=2048,256,2**40
    ans={}
    for name,q in [('minus',F(1,16)),('midpoint',F(1,8)),('plus',F(3,16))]:
        probability=F(comb(n,k))*q**k*(1-q)**(n-k)
        ans[name]={'prior':str(q),'trigger_probability':float(probability),
                   'expected_work':float(n+extra*probability)}
    return {'initial_fresh_labels':n,'trigger_positive_count':k,
            'extra_observations_when_triggered':extra,'populations':ans,
            'meaning':'Counterexample to replacing midpoint work by average endpoint work; NOT a counterexample to C.2.'}


def overlapping_localization_check():
    # Two overlapping fractional submeasures on the SAME two magnitudes.
    mu=[F(1,2),F(1,2)]
    sigmas=[[F(1,4),F(1,8)],[F(1,8),F(1,4)]]
    taus=[sum(s) for s in sigmas]
    nu=[[v/t for v in s] for s,t in zip(sigmas,taus)]
    residual=[mu[j]-sum(s[j] for s in sigmas) for j in range(2)]
    gaps=[F(1,4),F(1,8)]
    low=[[F(1,16),F(1,32)],[F(1,32),F(1,16)]]
    high=[[F(3,16),F(1,8)],[F(1,8),F(3,16)]]
    rs=[F(1,4),F(1,4)]
    assert sum(t*r for t,r in zip(taus,rs))<=F(1,4)
    cases=0
    targetgaps=[]
    for endpoint in (low,high):
        q=[sum(sigmas[i][j]*endpoint[i][j] for i in range(2))/mu[j]
           for j in range(2)]
        theta=sum(w*x for w,x in zip(mu,q))
        assert theta==sum(taus[i]*sum(nu[i][j]*endpoint[i][j] for j in range(2))
                          for i in range(2))
        assert all(0<=x<=F(1,2) for x in q) and theta<=F(1,4)
        targetgaps.append(theta)
        for n in range(9):
            for k in range(n+1):
                direct=mixture=F(0)
                for j,d in enumerate(gaps):
                    pm,pp=F(1,2)-d,F(1,2)+d
                    bm,bp=pm**k*(1-pm)**(n-k),pp**k*(1-pp)**(n-k)
                    direct+=mu[j]*((1-q[j])*bm+q[j]*bp)
                    mixture+=residual[j]*bm
                    mixture+=sum(sigmas[i][j]*((1-endpoint[i][j])*bm+endpoint[i][j]*bp)
                                 for i in range(2))
                assert direct==mixture
                cases+=1
    def prob(masses,qs,word):
        n,k=len(word),sum(word)
        return sum(mass*((1-q)*(F(1,2)-d)**k*(F(1,2)+d)**(n-k)
                         +q*(F(1,2)+d)**k*(F(1,2)-d)**(n-k))
                   for mass,d,q in zip(masses,gaps,qs))
    residual_mass=sum(residual)
    residual_law=[w/residual_mass for w in residual]
    qlo=[sum(sigmas[i][j]*low[i][j] for i in range(2))/mu[j] for j in range(2)]
    qhi=[sum(sigmas[i][j]*high[i][j] for i in range(2))/mu[j] for j in range(2)]
    for seed in range(20263000,20263100):
        rng=random.Random(seed)
        leaves=[]
        def grow(word):
            if len(word)==6 or (word and rng.randrange(4)==0):
                leaves.append(word)
            else:
                grow(word+(0,));grow(word+(1,))
        grow(())
        original_h=hellinger_interval([prob(mu,qlo,w) for w in leaves],
                                      [prob(mu,qhi,w) for w in leaves])
        mixture_h_lower=F(0)
        mixture_null_work=F(0)
        for i in range(2):
            hlo,hhi=hellinger_interval([prob(nu[i],low[i],w) for w in leaves],
                                      [prob(nu[i],high[i],w) for w in leaves])
            mixture_h_lower+=taus[i]*hlo
            mixture_null_work+=taus[i]*sum(len(w)*prob(nu[i],[0,0],w) for w in leaves)
        mixture_null_work+=residual_mass*sum(len(w)*prob(residual_law,[0,0],w) for w in leaves)
        assert original_h[1]<=mixture_h_lower
        assert mixture_null_work==sum(len(w)*prob(mu,[0,0],w) for w in leaves)
    return {'overlapping_components':2,'prefix_kernel_identities':cases,
            'stopped_policies_testing_direct_Hellinger_mixture_proof':100,
            'target_gap':str(targetgaps[1]-targetgaps[0]),'all_checks_passed':True}


def unbounded_interleaving_check():
    # Make both signs have mean in [1/8,7/8], giving uniform finite work.
    laws=[[(mass,min(d,F(3,8)),ql,qh) for mass,d,ql,qh in law]
          for law in TYPES[:2]]
    def prior(state,ql,qh):
        return {'lo':ql,'hi':qh,'mid':(ql+qh)/2}[state]
    @lru_cache(None)
    def kern(typ,state,n,k):
        ans=F(0)
        for mass,d,ql,qh in laws[typ]:
            q=prior(state,ql,qh)
            pm,pp=F(1,2)-d,F(1,2)+d
            ans+=mass*((1-q)*pm**k*(1-pm)**(n-k)+q*pp**k*(1-pp)**(n-k))
        return ans
    def geometric_work(state,cap=None):
        value=F(0)
        for first in (0,1):
            conditional=F(0)
            for mass,d,ql,qh in laws[first]:
                q=prior(state,ql,qh)
                for prob,weight in ((F(1,2)-d,1-q),(F(1,2)+d,q)):
                    conditional+=mass*weight*(1 if cap is None else 1-(1-prob)**cap)/prob
            value+=2*kern(0,state,1,first)*conditional
        return value
    # A universal local coefficient from revealing the full latent state.
    kappas=[]
    for law in laws:
        affinity_lower=F(0)
        for mass,d,ql,qh in law:
            affinity_lower+=mass*(sqrt_interval(ql*qh)[0]
                                  +sqrt_interval((1-ql)*(1-qh))[0])
        kappas.append(1-affinity_lower)
    kappa=max(kappas)
    rows=[]
    for cap in (1,2,4,8,16,32,64):
        minus=[];plus=[];mid=[]
        # Sample unit 0, choose unit 1's type from that first bit, and then
        # alternate units until unit 1 produces its first head. T=2*K.
        for k in range(1,cap+1):
            for first in (0,1):
                for j in range(k):
                    coeff=F(comb(k-1,j))
                    for state,out in (('lo',minus),('hi',plus),('mid',mid)):
                        out.append(coeff*kern(0,state,k,j+first)*kern(first,state,k,1))
        tail={state:F(0) for state in ('lo','hi','mid')}
        for first in (0,1):
            for j in range(cap):
                coeff=F(comb(cap-1,j))
                for state,out in (('lo',minus),('hi',plus),('mid',mid)):
                    probability=coeff*kern(0,state,cap,j+first)*kern(first,state,cap,0)
                    out.append(probability)
                    tail[state]+=probability
        assert sum(minus)==sum(plus)==sum(mid)==1
        hlo,hhi=hellinger_interval(minus,plus)
        work=geometric_work('mid',cap)
        assert hhi<=kappa*work
        assert all(t<=(F(7,8)**cap) for t in tail.values())
        rows.append({'total_cap':2*cap,'midpoint_expected_work':float(work),
                     'Hellinger_h_upper':float(hhi),
                     'endpoint_tail_probabilities':{state:float(tail[state]) for state in ('lo','hi')},
                     'TV_coupling_error_bound':float(tail['lo']+tail['hi'])})
    fullwork={state:geometric_work(state) for state in ('lo','hi','mid')}
    assert all(x<=16 for x in fullwork.values())
    return {'policy':'First bit selects second-unit type; alternate revisits until second unit first returns head.',
            'stopping':'Unbounded, observation dependent; T=2*K.',
            'uniform_expected_work_bound_for_all_component_priors':16,
            'exact_expected_work':{state:str(value) for state,value in fullwork.items()},
            'caps':rows,'all_checks_passed':True}


if __name__=='__main__':
    print(json.dumps({'finite_trees':finite_tree_checks(),
                      'seed_realizations':seed_realization_checks(),
                      'endpoint_work_counterexample':endpoint_work_counterexample(),
                      'overlapping_localization':overlapping_localization_check(),
                      'unbounded_interleaving':unbounded_interleaving_check()},indent=2))
