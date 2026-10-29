"""Exact checks for new constants and examples; no nonstandard dependencies."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json,re


def log_bounds(x, terms=90):
    assert x>0
    shift=0
    while x<1:x*=2;shift-=1
    while x>=2:x/=2;shift+=1
    def reduced(z):
        y=(z-1)/(z+1)
        lower=2*sum((y**(2*j+1)/F(2*j+1) for j in range(terms)),F())
        error=2*y**(2*terms+1)/F(2*terms+1)/(1-y*y)
        return lower,lower+error
    lo,hi=reduced(x);l2,u2=reduced(F(2))
    return (lo+shift*l2,hi+shift*u2) if shift>=0 else (lo+shift*u2,hi+shift*l2)


def sqrt_bounds(x, digits=18):
    scale=10**digits
    k=isqrt(x.numerator*scale**2//x.denominator)
    return F(k,scale),F(k+1,scale)


def entropy_bounds(a):
    A=sum(a,F());lo=hi=A
    if not A:return F(),F()
    for x in a:
        if x:
            l,u=log_bounds(A/x);lo+=x*l;hi+=x*u
    return lo,hi


def run():
    eps=F(1,1024);rho=F(1,4);h=F(1,1024)
    gaps=[F(1,2),F(1,4),F(1,8)]
    weights=[(1-eps)/2,eps,(1-eps)/2]
    rows=[]
    for mask in range(8):
        chosen=[i for i in range(3) if mask>>i&1]
        lo,hi=entropy_bounds([weights[i]/gaps[i]**2 for i in chosen])
        lo=sqrt_bounds(rho*lo)[0];hi=sqrt_bounds(rho*hi)[1]
        remainder=sum((weights[i]/gaps[i] for i in range(3) if i not in chosen),F())
        lo+=remainder;hi+=remainder
        rows.append({'mask':mask,'retained_gaps':[str(gaps[i]) for i in chosen],
                     'cost_over_h_lower':str(lo),'cost_over_h_upper':str(hi),
                     'approx':float((lo+hi)/2)})
    winner=rows[5]
    assert F(winner['cost_over_h_upper']) < min(F(r['cost_over_h_lower']) for r in rows if r['mask']!=5)
    assert h*F(winner['cost_over_h_upper'])<rho
    loglo,loghi=log_bounds(F(25,3))
    weighted_lo=65+F(40,3)*(9+loglo)
    weighted_hi=65+F(40,3)*(9+loghi)
    assert weighted_hi<214
    assert 4*214==856 and 856*1040==890240 and F(3,2)*890240<2_000_000
    assert 2*(24576+896*128*32*1500*3**14)<10**17
    upper_gamma=F(165,32)*20
    upper_H=F(165,32)*(F(514,3)+F(3,2)*(3328+10))
    assert max(upper_gamma,upper_H,128)<33000
    tails=[]
    for J in (8,32,128,512):
        ordinary=sum((F(2**j,2**J*j*(j+1)) for j in range(1,J+1)),F())
        assert ordinary <= F(8,J*J)+F(1,2**(J//2))
        tails.append({'J':J,'ignored_mass':str(F(1,J+1)),
                      'ordinary_cost':str(ordinary),'upper_functional':float(F(1,J+1)+ordinary)})
    root=Path(__file__).resolve().parents[1]
    tex='\n'.join(p.read_text(encoding='utf-8') for p in [root/'main.tex',*sorted((root/'sections').glob('*.tex'))])
    labels=re.findall(r'\\label\{([^}]+)\}',tex)
    refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',tex)
    assert len(set(labels))==len(labels),'duplicate labels'
    assert not set(refs)-set(labels),set(refs)-set(labels)
    assert not re.search(r'[\x00-\x08\x0b\x0c\x0e-\x1f]',tex),'control character in TeX'
    assert '{257}' not in tex and r'1\,069\,120' not in tex
    assert r'hH_O\le2\Psi' in tex and r'w_j\le\rho' in tex
    assert r'3\Psi(h)' in tex and r'10\Psi(h)' not in tex
    result={'status':'PASS','noninterval_example':{'gaps':list(map(str,gaps)),'weights':list(map(str,weights)),
      'rho':str(rho),'h':str(h),'unique_winner_mask':5,'assignments':rows},
      'weighted_constant':{'coefficient_lower':str(weighted_lo),'coefficient_upper':str(weighted_hi),
       'coefficient_approx':float((weighted_lo+weighted_hi)/2),'replacement_denominator':214,
       'annular_factors':[856,890240],'conservative_annular_denominator':2_000_000},
      'main_constants':{'lower':str(F(1,10**17)),'upper':33000,
       'upper_entropy_rational_bound':str(upper_gamma),'upper_ordinary_rational_bound':str(upper_H)},
      'infinite_tail_examples':tails,'tex_integrity':{'labels':len(labels),'references':len(refs),'missing':0,'duplicates':0},
      'scope':'Exact new finite examples and arithmetic; not formal verification of general mathematical statements.'}
    (Path(__file__).with_name('revision_checks.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','winner':winner,'weighted_constant':float(weighted_hi),
                      'labels':len(labels),'references':len(refs)},indent=2))

if __name__=='__main__':run()
