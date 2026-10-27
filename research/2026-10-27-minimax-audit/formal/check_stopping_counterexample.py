"""Exact rational finite-prefix checks, not an infinite-horizon certificate."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent

def check(p, cap):
    live={0:F(1)}
    hits={}
    for n in range(1,cap+1):
        following={}
        hit=F(0)
        for x,mass in live.items():
            for y,weight in [(x+1,p),(x-1,1-p)]:
                if y==1:
                    hit+=mass*weight
                else:
                    following[y]=following.get(y,F(0))+mass*weight
        hits[n]=hit
        expected=F(0) if n%2==0 else F(comb(n-1,(n-1)//2),(n+1)//2)*p**((n+1)//2)*(1-p)**((n-1)//2)
        assert hit==expected
        live=following
        assert sum(hits.values())+sum(live.values())==1
    eventual=F(1) if p>F(1,2) else p/(1-p)
    assert sum(hits.values())<=eventual
    return {"p":str(p),"cap":cap,"hit_mass":str(sum(hits.values())),
        "unresolved_mass":str(sum(live.values())),
        "partial_first_moment":str(sum(n*x for n,x in hits.items())),
        "paper_eventual_hit_probability":str(eventual),
        "paper_nontermination_probability":str(1-eventual),
        "hit_mass_decimal_for_display":float(sum(hits.values()))}

if __name__=="__main__":
    record={"status":"NUMERICAL: exact rational finite-prefix arithmetic",
            "seed":None,"precision":"Python Fraction, exact integers and rationals",
            "scope":"Catalan first-hit formula through cap 101; unresolved mass retained",
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "cases":[check(F(5,8),101),check(F(3,8),101)]}
    (HERE/"stopping_counterexample_checks.json").write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps({"checked_steps":202,"caps":[101,101],"all_equalities_exact":True}))
