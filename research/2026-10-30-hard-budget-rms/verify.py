"""Exact finite audits of fallback accounting; not a universal proof checker."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import random
import sys
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'toolkit'))
from threshold_toolkit.budget_ladders import stage, plan

def recurrence_audit():
    rng=random.Random(2026103003)
    instances=branches=0
    largest_ratio=F(0)
    for count in range(1,8):
        for case in range(8):
            upper=F(1,4); theta=F(rng.randrange(5),16)
            old=upper/2
            laws=[]
            c2=F(1,4)
            full_moments=[]
            for j in range(count):
                s=stage(j); p=F(1,8) if case%2 else F(1,16)
                amplitude=upper/F(2**(1+(j//2)))
                y1=max(F(0),min(upper,theta+amplitude))
                y2=max(F(0),min(upper,theta-amplitude/2))
                # Failures carry a perfect *eventual* output, but cost cap+1.
                # This deliberately correlates output error and runtime.
                law=[((1-p)/2,0,y1,False),((1-p)/2,s.expected_budget//2,y2,False),
                     (p,s.flip_cap+1,theta,True)]
                assert sum(z[0] for z in law)==1
                assert sum(prob*cost for prob,cost,_,_ in law)<=s.expected_budget
                mse=sum(prob*(y-theta)**2 for prob,_,y,_ in law)
                f2=upper*upper/F(2*s.expected_budget)
                c2=max(c2,mse/f2)
                full_moments.append(mse)
                laws.append(law)
            explicit=F(0)
            for choices in product(*laws):
                prob=F(1); out=old
                for pr,_,y,failed in choices:
                    prob*=pr
                    if not failed: out=y
                explicit+=prob*(out-theta)**2
                branches+=1
            rec=(old-theta)**2
            bound=rec
            for law,full in zip(laws,full_moments):
                failure=sum(pr for pr,_,_,failed in law if failed)
                successful=sum(pr*(y-theta)**2 for pr,_,y,failed in law if not failed)
                rec=successful+failure*rec
                bound=full+F(1,4)*bound
            assert explicit==rec<=bound
            # Any allowance before the next checkpoint uses these same stages.
            for B in [stage(count-1).checkpoint,stage(count).checkpoint-1]:
                fB2=upper*upper/F(2*B)
                assert explicit<=32*c2*fB2
                largest_ratio=max(largest_ratio,explicit/(c2*fB2))
            instances+=1
    return {'instances':instances,'enumerated_independent_outcome_paths':branches,
            'recurrence_identities':instances,'work_premise_checks':sum(8*k for k in range(1,8)),
            'constant_bound_checks':2*instances,
            'largest_squared_normalized_ratio':str(largest_ratio),
            'universal_theorem_proved_by_finite_check':False}

def bad_timeout_audit():
    rho=F(1,4); p=F(1,8)
    entries=[]
    for m in [2,3,5,8,10,13]:
        n=stage(m).checkpoint
        good=(rho/2)**2*p**(m-1)
        bad=(rho/2)**2*p
        assert good<=bad
        entries.append({'last_stage':m,'authorized_budget':n,
                        'independent_ladder_mse_at_theta_zero':str(good),
                        'one_shot_or_shared_delay_mse_at_theta_zero':str(bad)})
    return {'scope':'exact analytic calculations for delayed iid-Bernoulli sample means',
            'rho':str(rho),'delay_probability':str(p),'records':entries}

def schedule_audit():
    checked = 0
    for B in list(range(10001)) + [10**k for k in range(1, 301)]:
        s = plan(B)
        assert sum(t.flip_cap for t in s) <= B
        assert stage(len(s)).checkpoint > B
        if s:
            assert 4*s[-1].flip_cap > B
            m = s[-1].index
            coefficient = F(B, s[-1].expected_budget)*sum(F(1, 2)**k for k in range(m+2))
            assert coefficient < 32
        checked += 1
    return {'budgets_checked': checked, 'largest_budget_decimal_exponent': 300}


def main():
    if not __debug__:
        raise RuntimeError('Run without -O.')
    data = {'status': 'passed', 'scope': 'finite_rational_checks_not_universal_proof',
            'recurrence': recurrence_audit(), 'schedules': schedule_audit(),
            'timeout_counterexamples': bad_timeout_audit()}
    target = ROOT / '.runtime/hard-budget-rms/validation.json'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
