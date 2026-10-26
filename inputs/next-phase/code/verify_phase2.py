"""Deterministic diagnostics and implementation checks; NOT proofs of rates."""
from __future__ import annotations
import json,math,sys
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import minimize
from rare_event import atomic_psi,shifted_increment,power_plan
ROOT=Path(__file__).resolve().parents[1]; RES=ROOT/'results'
sys.path.insert(0,str(ROOT/'baseline/Adaptive_Threshold_v4/code'))
from threshold import coupled_increment,decision

def main():
    rng=np.random.default_rng(20261026);out={'status':'numerical diagnostics, not mathematical proof'}
    # Epigraph SOCP written as smooth SLSQP inequalities: maximize sum mass*z,
    # 0<=z<=w and z^2<=h^2*w/d^2, mass*w<=rho. Independent of closed-form optimizer.
    optim=[]
    for k in range(24):
        n=int(rng.integers(2,9));d=np.exp(rng.uniform(np.log(.008),np.log(.5),n));mass=rng.dirichlet(np.ones(n));rho=float(rng.uniform(.02,.25));h=float(np.exp(rng.uniform(np.log(.002),np.log(.2))))
        psi,t,w=atomic_psi(d,mass,rho,h);nvar=n
        def objective(x):return -mass@x[nvar:]
        constraints=[{'type':'ineq','fun':lambda x,mass=mass,rho=rho:rho-mass@x[:nvar]},
          {'type':'ineq','fun':lambda x:x[:nvar]-x[nvar:]},
          {'type':'ineq','fun':lambda x,h=h,d=d:(h/d)**2*x[:nvar]-x[nvar:]**2}]
        x0=np.r_[np.full(n,rho*.5),np.minimum(rho*.5,h*np.sqrt(rho*.5)/d)*.9]
        fit=minimize(objective,x0,method='SLSQP',bounds=[(0,1)]*(2*n),constraints=constraints,
                     options={'ftol':1e-11,'maxiter':2000})
        difference=abs(-fit.fun-psi);feasible=min(float(np.min(c['fun'](fit.x))) for c in constraints)
        optim.append(dict(n=n,rho=rho,h=h,psi=psi,numerical=-float(fit.fun),difference=difference,
                          solver_success=bool(fit.success),min_constraint=feasible,budget_error=abs(float(mass@w)-rho)))
    assert max(x['difference'] for x in optim)<2e-6
    out['variational_optimization']=optim
    # Power integrals, split exactly at their only change point.
    checks=[]
    for alpha in [.3,.7,1.,1.4,1.8]:
      a=.25;ke=4/(4-alpha);km=1+alpha/(2-alpha)+2*alpha/(2-alpha)**2
      for z in [2.,10.,100.,1000.]: # z=sqrt(n)*a
        n=(z/a)**2;cut=1/math.sqrt(n)
        den=lambda d:alpha*d**(alpha-1)/a**alpha
        en=(cut/a)**alpha+quad(lambda d:(n*d*d)**-2*den(d),cut,a,epsabs=1e-12)[0]
        mn=n*(cut/a)**alpha+quad(lambda d:(1+math.log(n*d*d))/(d*d)*den(d),cut,a,epsabs=1e-10)[0]
        eb=ke*a**-alpha*n**(-alpha/2);mb=km*a**-alpha*n**(1-alpha/2)
        checks.append(dict(alpha=alpha,z=z,error_ratio=en/eb,work_ratio=mn/mb))
    assert max(v['error_ratio'] for v in checks)<=1+1e-10
    assert max(v['work_ratio'] for v in checks)<=1+1e-10
    out['power_integral_bounds']=checks
    # Implementation coupling: identical prefix, no random sampling approximation.
    agree=0
    for level in range(9):
      for trial in range(30):
        bits=rng.integers(0,2,size=1<<level)
        def callback():
          cursor=0
          def f(k):
            nonlocal cursor
            ans=int(bits[cursor:cursor+k].sum());cursor+=k;return ans
          return f
        assert coupled_increment(level,callback())==shifted_increment(level,1,callback())
        agree+=1
    out['baseline_prefix_agreements']=agree
    # Arbitrary shifted base: directly evaluate each classifier on the same tape.
    direct=0
    for base in [2,8,32]:
      for j in range(5):
       for trial in range(20):
        cap=base<<j;bits=rng.integers(0,2,size=cap)
        def single(N):
          n=1
          while True:
            z=decision(int(bits[:n].sum()),n,N)
            if z is not None:return z,n
            n*=2
        z,n=single(cap);zc,nc=(0,0) if j==0 else single(cap//2)
        cursor=0
        def cb(k):
          nonlocal cursor
          val=int(bits[cursor:cursor+k].sum());cursor+=k;return val
        assert shifted_increment(j,base,cb)==(z-zc,max(n,nc));direct+=1
    out['shifted_prefix_agreements']=direct
    # Analytic counterexample constants and oracle information bound.
    counter=[]
    eta=1/64;klcap=32*eta**2/(1-4*eta**2)**2
    lecam=(2*eta)*math.sqrt((1-math.sqrt(klcap/2))/8)
    for rho in [1/16,1/64,1/256,1/1024]:
        d=rho*rho;B=rho**-4;h=(rho*B)**-.5
        heuristic=rho*(rho+(1-rho)*h/.25)
        counter.append(dict(rho=rho,d=d,B=B,heuristic=heuristic,proved_lower=lecam*rho,
                            lower_over_heuristic=lecam*rho/heuristic))
    assert lecam>.01
    out['counterexample']=dict(kl_bound=klcap,lower_coefficient=lecam,rows=counter)
    # Symbolic conditional means and variances of the GHA/Bernoulli conversion.
    tau,y,L=sp.symbols('tau y L', real=True)
    mean=tau*(y*y-1)-L;variance=2*tau**2+4*tau*(1-tau)*y*y
    out['model_identities']={'mean':str(mean),'variance_X':str(variance),
        'variance_symmetric_noise':str(sp.expand(variance+2*tau**2)),
        'symmetry_reason':'swap the two independent squared standard normals and negate the independent normal'}
    # Negative-binomial inverse moment identity is symbolic, inherited from v4.
    p=sp.symbols('p',positive=True);k=sp.symbols('k',integer=True,nonnegative=True)
    inv=sp.summation(p**2*(1-p)**k,(k,0,sp.oo))
    out['calibration_identity']='sum_{k>=0} p^2(1-p)^k=p for 0<p<=1'
    out['all_negative_variance_floor_d_quarter']=(.5-.25)/(1-2**-.5)
    # Non-simulated plans: conservative constants can demand very large bases.
    out['example_plans']=[dict(alpha=a,rho=r,B=2**25,plan=str(power_plan(2**25,r,a))) for a in [.5,1.,1.5] for r in [.1,.01]]
    (RES/'theory_diagnostics.json').write_text(json.dumps(out,indent=2))
    print('Optimizer comparisons:',len(optim),'maximum difference',max(x['difference'] for x in optim))
    print('Power quadrature bounds:',len(checks),'prefix checks:',agree+direct)
    print('Counterexample lower coefficient:',lecam)
if __name__=='__main__':main()
