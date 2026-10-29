"""Independent falsification checks of the 29 October manuscript revision.

Does not import the manuscript's verification code and does not alter the
manuscript. Exact Fraction checks are distinguished from numerical searches.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
from math import comb, factorial, log, sqrt
import hashlib, json, random

ROOT = Path(__file__).resolve().parent
SEED = 2026102901
rng = random.Random(SEED)

def dec(x):
    if isinstance(x, F): return D(x.numerator)/D(x.denominator)
    return D(str(x))

def G(a):
    a = [x for x in a if x]
    A = sum(a)
    return A + A*log(A) - sum(x*log(x) for x in a) if A else 0.0

def gd(a):
    a = [x for x in a if x]
    A = sum(a, D(0))
    return A*(1+A.ln())-sum((x*x.ln() for x in a),D(0)) if A else D(0)

def psi_candidate(gaps, weights, rho, h):
    lo,hi = 0.0,max(gaps)
    for _ in range(120):
        al=(lo+hi)/2
        mass=sum(w*min(1,(al/d)**2) for w,d in zip(weights,gaps))
        if mass>rho:hi=al
        else:lo=al
    al=(lo+hi)/2
    x=[min(1,(al/d)**2) for d in gaps]
    value=sum(w*min(v,h*sqrt(v)/d) for d,w,v in zip(gaps,weights,x))
    return value,al,x

def psi_dual(gaps,weights,rho,h):
    # Independently minimize the scalar convex dual. Its pointwise maximum
    # is evaluated at endpoints, the kink, and a stationary point.
    def objective(lam):
        total=lam*rho
        for d,w in zip(gaps,weights):
            c=h/d
            candidates=[0.,1.,min(1.,c*c)]
            if lam>0:candidates.append(min(1.,(c/(2*lam))**2))
            total+=w*max(min(v,c*sqrt(v))-lam*v for v in candidates)
        return total
    lo,hi=0.,.5
    for _ in range(110):
        m1=lo+(hi-lo)/3;m2=hi-(hi-lo)/3
        if objective(m1)<objective(m2):hi=m2
        else:lo=m1
    return min(rho,objective((lo+hi)/2),objective(0.))

def bellman(rewards, work, cap, price):
    values=list(rewards[cap])
    for n in range(cap-1,0,-1):
        values=[max(rewards[n][k],values[k]+values[k+1]-price*work[n][k])
                for k in range(n+1)]
    return values[0]+values[1]-price

def ratio(rewards,work,cap,hi):
    lo=0.
    for _ in range(65):
        mid=(lo+hi)/2
        if bellman(rewards,work,cap,mid)>0:lo=mid
        else:hi=mid
    return (lo+hi)/2

def continuous_genie_counterexample():
    N=64
    rewards=[];work=[];prefix_checks=0
    for n in range(N+1):
        rr=[];ww=[]
        for k in range(n+1):
            u=F(1,(n+1)*comb(n,k))
            low=u*F(sum(comb(n+1,j) for j in range(k+1,n+2)),2**(n+1))
            pv=F(2*(n-k+1),n+2)*u
            delta=u/2-low
            r=delta*delta/pv
            pw=u/2+low
            if n:
                assert r<=F(3*n,8)*u
                assert pw>=u/2
                prefix_checks+=1
            rr.append(r);ww.append(pw)
        rewards.append(rr);work.append(ww)
    exact_caps=[]
    for cap in (1,2,4,8,16,32,64):
        root=bellman(rewards,work,cap,F(3,4))
        assert root<=0
        ordinary=ratio([[float(v) for v in row] for row in rewards],
                       [[float(v) for v in row] for row in work],cap,.75)
        exact_caps.append({'cap':cap,'root_surplus_at_price_3_over_4':str(root),
                           'ordinary_optimal_ratio_numerical':ordinary})
    with localcontext() as ctx:
        ctx.prec=100
        regularized=[]
        for power in (16,64,128,256):
            eps=D(2)**(-power)
            cv=(((4-3*eps)/(4+3*eps))*((8-eps)/eps)).ln()/(8*(1-eps))
            ordinary_upper=D(3)/(4*(1-eps))
            regularized.append({'epsilon':'2^-'+str(power),'C_v':str(cv),
                'cap_8_genie_ratio_lower':str(cv/8),
                'ordinary_infinite_ratio_upper':str(ordinary_upper)})
        assert D(regularized[-1]['cap_8_genie_ratio_lower'])>D(regularized[-1]['ordinary_infinite_ratio_upper'])
    return {'exact_ordered_prefix_inequalities':prefix_checks,
            'exact_bellman_certificates':exact_caps,
            'regularization_nonuniformity':regularized,
            'analytic_divergence':'At cutoff d=1/2-2^-m, partial C_v = log(2^m-1)/8 >= (m-1)log(2)/8.'}

def finite_genie_trials():
    worst=0.;runs=0
    for t in range(36):
        gaps=[.5,.125,1/128] if t else [.5]
        weights=[.4,.3,.3] if t else [1.]
        def prior():
            q=[rng.random() for _ in gaps]
            s=sum(w*x for w,x in zip(weights,q))
            scale=min(1.,.25/s)
            return [x*scale for x in q]
        ql,qh,qv,qw=[prior() for _ in range(4)]
        if t%4==1:qv=[x*1e-5 for x in qv]
        delta=[b-a for a,b in zip(ql,qh)]
        cv=sum(w*z*z/(v*(1-v)) for w,z,v in zip(weights,delta,qv))
        rs=[];gs=[];ws=[]
        for n in range(9):
            rr=[];gg=[];ww=[]
            for k in range(n+1):
                plus=[(.5+d)**k*(.5-d)**(n-k) for d in gaps]
                minus=[(.5-d)**k*(.5+d)**(n-k) for d in gaps]
                pd=sum(w*z*(a-b) for w,z,a,b in zip(weights,delta,plus,minus))
                pv=sum(w*(v*a+(1-v)*b) for w,v,a,b in zip(weights,qv,plus,minus))
                pw=sum(w*(v*a+(1-v)*b) for w,v,a,b in zip(weights,qw,plus,minus))
                gg.append(sum(w*z*z*(a/v+b/(1-v)) for w,z,v,a,b in zip(weights,delta,qv,plus,minus)))
                rr.append(pd*pd/pv if pv else 0.);ww.append(pw)
            rs.append(rr);gs.append(gg);ws.append(ww)
        last_k=0.;last_g=float('inf')
        for n in range(1,9):
            k=ratio(rs,ws,n,cv)
            genie=ratio(rs[:n]+[gs[n]],ws,n,cv)
            residual=cv-sum(comb(n,j)*rs[n][j] for j in range(n+1))
            tol=2e-10*max(1.,cv)
            assert k>=last_k-tol and genie<=last_g+tol
            assert genie>=k-tol and genie-k<=residual+tol
            worst=max(worst,(genie-k-residual)/max(1.,cv))
            last_k,last_g=k,genie;runs+=1
    return {'quadruples':36,'cap_comparisons':runs,'largest_scaled_residual_bound_violation':worst,
            'method':'Floating-point Bellman optimization; includes deterministic perfect-label support and near-singular variance references.'}

def numerical_selection_trials():
    maxmass=0.;maxordinary=0.;examples=0
    near_ties=0
    for _ in range(700):
        n=rng.randint(2,8)
        indices=sorted(rng.sample(range(22),n))
        gaps=[2.**(-j-1) for j in indices]
        raw=[2.**rng.uniform(-15,0) for _ in range(n)]
        weights=[w/sum(raw) for w in raw]
        rho=2.**rng.uniform(-16,-2)
        h=2.**rng.uniform(-25,0)
        a=[w/d**2 for w,d in zip(weights,gaps)]
        costs=[]
        for mask in range(1<<n):
            costs.append(h*sqrt(rho*G([v for j,v in enumerate(a) if mask>>j&1]))+
                         sum(w*min(1.,h/d) for j,(w,d) in enumerate(zip(weights,gaps)) if not(mask>>j&1)))
        best=min(range(1<<n),key=costs.__getitem__)
        O=[j for j,d in enumerate(gaps) if not(best>>j&1) and d>=h]
        # Resolve any suspicious float-selected minimizer independently at
        # 80 decimal digits before classifying a putative counterexample.
        if O and max(weights[j]/rho for j in O)>1+1e-8:
            near_ties+=1
            with localcontext() as ctx:
                ctx.prec=80
                wd=list(map(dec,weights));dd=list(map(dec,gaps));rd=dec(rho);hd=dec(h)
                cd=[]
                for mask in range(1<<n):
                    cd.append(hd*(rd*gd([w/d**2 for j,(w,d) in enumerate(zip(wd,dd)) if mask>>j&1])).sqrt()+
                        sum((w*min(D(1),hd/d) for j,(w,d) in enumerate(zip(wd,dd)) if not(mask>>j&1)),D(0)))
                best=min(range(1<<n),key=cd.__getitem__)
                O=[j for j,d in enumerate(gaps) if not(best>>j&1) and d>=h]
        p,_,_=psi_candidate(gaps,weights,rho,h)
        mass=max((weights[j]/rho for j in O),default=0.)
        ordinary=sum(h*weights[j]/gaps[j] for j in O)/p
        assert mass<=1+1e-8,(gaps,weights,rho,h,best,mass)
        assert ordinary<=2+1e-8,(gaps,weights,rho,h,best,ordinary)
        maxmass=max(maxmass,mass);maxordinary=max(maxordinary,ordinary)
        examples+=len(costs)
    maxdual=0.
    for _ in range(100):
        n=rng.randint(1,10)
        gaps=[2.**rng.uniform(-20,-1) for _ in range(n)]
        raw=[rng.random() for _ in range(n)];weights=[w/sum(raw) for w in raw]
        rho=rng.uniform(.0001,.9999);h=2.**rng.uniform(-25,0)
        candidate,alpha,x=psi_candidate(gaps,weights,rho,h)
        dual=psi_dual(gaps,weights,rho,h)
        err=abs(candidate-dual)/max(1e-20,candidate)
        maxdual=max(maxdual,err)
        assert err<2e-9,(candidate,dual)
    # The standalone factor 2 in the dyadic top-mass lemma is sharp.
    ratios=[]
    for n in (2,8,32,128):
        total=sum((F(1,n)*2**j for j in range(n)),F())
        selected=F(1,n)*2**(n-1)
        ratios.append({'bands':n,'total_over_top_mass':str(total/selected)})
        assert total/selected==2-F(1,2**(n-1))
    return {'laws':700,'enumerated_hard_assignments':examples,
            'max_ordinary_band_mass_over_rho':maxmass,'max_h_H_O_over_Psi':maxordinary,
            'suspicious_float_minimizers_rechecked_at_80_digits':near_ties,
            'optimizer_dual_comparisons':100,'maximum_relative_primal_dual_gap':maxdual,
            'exact_dyadic_factor_two_examples':ratios}

def new_examples_and_constants():
    with localcontext() as ctx:
        ctx.prec=100
        eps=D(1)/1024;rho=D(1)/4;h=D(1)/1024
        ds=[D(1)/2,D(1)/4,D(1)/8];ws=[(1-eps)/2,eps,(1-eps)/2]
        costs=[]
        for mask in range(8):
            val=(rho*gd([w/d**2 for j,(w,d) in enumerate(zip(ws,ds)) if mask>>j&1])).sqrt()
            val+=sum((w/d for j,(w,d) in enumerate(zip(ws,ds)) if not(mask>>j&1)),D(0))
            costs.append(val)
        ordered=sorted(range(8),key=costs.__getitem__)
        assert ordered[:2]==[5,7]
        assert h*max(costs)<rho
        intervals=[('4.99902','4.99903'),('4.70676','4.70677'),('5.05761','5.05762'),
                   ('4.72155','4.72156'),('3.82997','3.82998'),('3.22748','3.22749'),
                   ('3.83271','3.83272'),('3.22943','3.22944')]
        assert all(D(l)<v<D(u) for (l,u),v in zip(intervals,costs))
        # Check fractional retained assignments as well as the eight vertices.
        fractional=0
        for i in range(13):
            for j in range(13):
                for k in range(13):
                    x=list(map(lambda z:D(z)/12,(i,j,k)))
                    v=(rho*gd([w*t/d**2 for w,t,d in zip(ws,x,ds)])).sqrt()
                    v+=sum((w*(1-t)/d for w,t,d in zip(ws,x,ds)),D(0))
                    assert v>=costs[5]-D('1e-95')
                    fractional+=1
        sign=65+D(40)/3*(9+(D(25)/3).ln())
        ann=dec(F(3,2)*890240)
        entropy=D(5)*D(17).sqrt()/4*(4*D(80).sqrt()/9+2*D(42).sqrt()+2)
        ordinary=D(5)*D(17).sqrt()/4*(D(2)/3+D(2).sqrt()*(3328+2*D(21).sqrt())+D(512)/3)
        cann=(-D(28)).exp()/2000000
        cE=cann.sqrt()/(896*128*32)
        low=1/(2*(24576+1/cE))
        highratio=64*(1+D(6).ln()).sqrt()
        assert sign<214 and ann<2000000
        assert entropy<104 and ordinary<27000
        assert cE<1/(D(896)*128*65536)
        assert highratio<112 and low>D('1e-17')
        assert 1/(2*D(8192)*115)>low and 1/D(8192)>low
        # Every annular branch still permits the common conservative constant.
        assert F(3,2)*256*F(64,3)<2000000
        assert F(3,2)*576<2000000
        assert F(3,2)*890240<2000000
        constants={'sign_entropy_coefficient':str(sign),'annular_denominator_required':str(ann),
                   'upper_entropy_coefficient':str(entropy),'upper_ordinary_coefficient':str(ordinary),
                   'packed_lower_coefficient_cE':str(cE),'assembled_lower_coefficient':str(low),
                   'high_gap_multiplier_upper':str(highratio)}
        # The sharp-bias example meets b <= rho/64 and defeats every c<4.
        sharp=[]
        for power in (12,20,40):
            d=F(1,2**power);ep=F(1,1024);r=F(1,8);b=ep*(1-2*d)/4
            assert b<=r/64
            for q in (F(0),F(1,4),F(1,2)):
                bias=ep*(F(1,2)-d)*(1-2*q)-b
                assert -b<=bias<=b
            # Taking c=3 gives a concrete numerical failure of the changed bound.
            false_rhs=(ep-3*b)**2/(192*d*d)
            sharp.append({'d':str(d),'bias':str(b),'c_3_false_lower_bound':str(false_rhs),
                          'actual_V_times_W_upper':'1/4'})
        assert F(sharp[-1]['c_3_false_lower_bound'])>F(1,4)
    return {'noninterval_costs_divided_by_h':[str(x) for x in costs],
            'unique_winner_mask':5,'runner_up_mask':7,'winner_margin_over_h':str(costs[7]-costs[5]),
            'fractional_grid_assignments':fractional,'constants':constants,'sharp_bias_example':sharp,
            'tail_proof':'For j<=J/2 the ordinary sum is <=2^(-floor(J/2)); for j>J/2 it is <=8/J^2. The tail allocation is feasible when 1/(J+1)<=rho and gives Psi>=1/(J+1).'}

def main():
    result={'seed':SEED,'status':'PASS','new_examples_and_constants':new_examples_and_constants()}
    print('Examples, fractional grid, sharp-bias witness, and constant chain passed.',flush=True)
    result['selection_and_variational_optimizer']=numerical_selection_trials()
    print('Independent selection and scalar-dual stress checks passed.',flush=True)
    result['continuous_genie_counterexample']=continuous_genie_counterexample()
    print('Exact prefix inequalities and Bellman certificates for genie example passed.',flush=True)
    result['finite_divergence_genie']=finite_genie_trials()
    result['revised_pdf_sha256']=hashlib.sha256((ROOT/'pdf/adaptive_rare_event_estimation_revised.pdf').read_bytes()).hexdigest()
    result['scope']='Independent arithmetic, exact finite-prefix certificates and numerical falsification searches. General conclusions additionally rely on the analytic derivations in the audit.'
    target=ROOT/'revised_changes_adversarial_audit_results.json'
    target.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('PASS: '+str(target),flush=True)

if __name__=='__main__':main()
