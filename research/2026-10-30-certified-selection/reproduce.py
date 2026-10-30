"""Reproduce the new deterministic checks; no repository held-out data used."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'toolkit'))
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw, Precision, evaluate_selection, exhaustive_certificate,
    quantile_certificate, suffix_search_size, verify_certificate, threshold_certificate,
)

OUT=Path(__file__).resolve().parent/'evidence'
P=Precision(bits=64,log_terms=24)

def bounds(c):
    return [F(c['K_interval'][k]) for k in ['lower','upper']]

def summarize(c):
    l,u=bounds(c)
    return {'lower_decimal_display':float(l),'upper_decimal_display':float(u),
            'width_decimal_display':float(u-l),
            'scope':'decimal displays only; exact endpoints are in the certificate'}

def main():
    OUT.mkdir(exist_ok=True)
    cases={
      'selection_essential':(FiniteGapLaw([('1/10000000000','1/100000000'),('1/4','99999999/100000000')]),F(1,10**6),F(10**12)),
      'not_one_global_threshold':(FiniteGapLaw([('1/4','9999/10000'),('1/2','1/10000')]),F(1,4),F(10**8)),
      'cross_boundary_before':(FiniteGapLaw([('249/1000','1/2'),('251/1000','1/2')]),F(1,100),F(10**8)),
      'cross_boundary_after':(FiniteGapLaw([('251/1000',1)]),F(1,100),F(10**8)),
      'sixty_atoms_one_band':(FiniteGapLaw([(F(101+i,400),F(1,60)) for i in range(60)]),F(1,20),F(10**6)),
      'stress_near_max':(FiniteGapLaw([(F(215282,10**9),F(413943,10**6)),
            (F(316030,10**9),F(14171,10**6)),(F(1250871,10**9),F(94956,10**6)),
            (F(22545179,10**9),F(21878,10**6)),(F(24956686,10**9),F(450979,10**6)),
            (F(328605066,10**9),F(4073,10**6))]),F(211300,10**6),1/F(1522870,10**12)**2),
    }
    summary={}
    start=time.perf_counter()
    for name,(law,rho,B) in cases.items():
        c=exhaustive_certificate(law,rho=rho,budget=B,precision=P)
        q=quantile_certificate(law,rho=rho,budget=B,precision=P)
        v=threshold_certificate(law,rho=rho,budget=B,precision=P)
        assert verify_certificate(v,law,rho=rho,budget=B)
        assert verify_certificate(c,law,rho=rho,budget=B)
        assert verify_certificate(q,law,rho=rho,budget=B)
        (OUT/(name+'.json')).write_text(json.dumps({'exhaustive':c,'quantile':q,'global_threshold':v},indent=2)+'\n')
        kl,ku=bounds(c)
        ql,qu=[F(q['details']['Q_interval'][s]) for s in ('lower','upper')]
        summary[name]={**summarize(c),'states':c['details']['states_evaluated'],
                       'Q_over_K_interval_decimal_display':[float(ql/ku),float(qu/kl)],
                       'best_hard_witness':c['details']['best_hard_witness'],
                       'global_threshold_upper_decimal_display':float(bounds(v)[1])}
    essential=cases['selection_essential'];law,rho,B=essential
    kl,ku=bounds(exhaustive_certificate(law,rho=rho,budget=B,precision=P))
    end0=evaluate_selection(law,[0,0],rho=rho,budget=B,precision=P)
    end1=evaluate_selection(law,[1,1],rho=rho,budget=B,precision=P)
    summary['selection_essential']['no_selection_baseline_over_K_lower']=float(min(end0.lower,end1.lower)/ku)
    law,rho,B=cases['stress_near_max']
    q=quantile_certificate(law,rho=rho,budget=B,precision=P)
    feasible=evaluate_selection(law,[1,0,1,1,1,1],rho=rho,budget=B,precision=P)
    qlower=F(q['details']['Q_interval']['lower'])
    gap=F(142132,100000)
    assert qlower>gap*feasible.upper and gap*gap>2
    (OUT/'sqrt2_counterexample.json').write_text(json.dumps({
        'scope':'exact finite counterexample to Q <= sqrt(2) K',
        'supporting_instance_file':'stress_near_max.json',
        'Q_lower':str(qlower),'feasible_objective_upper':str(feasible.upper),
        'feasible_selection':[1,0,1,1,1,1],
        'certified_Q_over_K_strict_lower_bound':str(gap),
        'rational_checks':['Q_lower > (142132/100000)*feasible_upper',
                           '(142132/100000)^2 > 2'],
        'depends_on_band_suffix_lemma':False},indent=2)+'\n')
    # Independent full-subset enumeration challenges the bandwise reduction.
    rng=random.Random(604219)
    gaps=[F(3,8),F(5,16),F(7,32),F(3,16),F(5,32),F(7,64),F(3,32),
          F(5,64),F(7,128),F(3,128),F(7,512),F(3,1024)]
    comparisons=0;full_states=0;suffix_states=0
    for trial in range(128):
        ds=rng.sample(gaps,rng.randint(2,8))
        raw=[rng.randrange(1,1001) for _ in ds];total=sum(raw)
        law=FiniteGapLaw([(d,F(w,total)) for d,w in zip(ds,raw)])
        rho=F(1,rng.choice([4,5,10,20,100,1000]))
        B=F(10**rng.randrange(0,13))
        intervals=[evaluate_selection(law,s,rho=rho,budget=B,precision=P)
                   for s in product((0,1),repeat=len(law.atoms))]
        bl=min(v.lower for v in intervals);bu=min(v.upper for v in intervals)
        c=exhaustive_certificate(law,rho=rho,budget=B,precision=P)
        kl,ku=bounds(c)
        assert kl<=bu and ku>=bl,('suffix',trial)
        q=quantile_certificate(law,rho=rho,budget=B,precision=P)
        ql,qu=bounds(q)
        assert ql<=bu and qu>=bl,('quantile',trial)
        comparisons+=1;full_states+=len(intervals);suffix_states+=suffix_search_size(law)
    record={'scope':'finite rational-interval regression evidence; not a proof of universal claims',
            'seed':604219,'laws_checked':comparisons,'full_subsets_evaluated':full_states,
            'band_suffix_candidates_evaluated':suffix_states,'counterexamples_found':0,
            'elapsed_seconds_including_examples':time.perf_counter()-start,'examples':summary}
    (OUT/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
