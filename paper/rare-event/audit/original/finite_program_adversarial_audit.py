"""Independent exact-rational audit of the finite stopping-flow characterization.

Uses no manuscript code or conic solver. Checks closed-form primal/dual
witnesses, exhaustive ordered stopping trees, flow aggregation/realization,
reference absorption, genie residuals, and the factor-sixteen cap arithmetic.
The two-atom example is a counterexample to using an arbitrary fixed cap,
not to the manuscript's explicitly chosen cap or genie stopping criterion.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, ceil, sqrt
from pathlib import Path
import json
import random

HALF = F(1, 2)


def expectation(mu, q):
    return sum((w*x for (_, w), x in zip(mu, q)), F())


def prefix(mu, q, n, k):
    return sum((w*((1-qi)*(HALF-d)**k*(HALF+d)**(n-k)
                   +qi*(HALF+d)**k*(HALF-d)**(n-k))
                for (d, w), qi in zip(mu, q)), F())


def rdiv(x, y):
    if y:
        return x*x/y
    if x:
        return None  # Infinite perspective.
    return F()


def coefficients(mu, quartet, N):
    low, high, variance, work = quartet
    rewards, costs, genie = {}, {}, {}
    for n in range(N+1):
        for k in range(n+1):
            delta = prefix(mu, high, n, k)-prefix(mu, low, n, k)
            rewards[n, k] = rdiv(delta, prefix(mu, variance, n, k))
            costs[n, k] = prefix(mu, work, n, k)
            g = F()
            for (d, w), ql, qh, qv in zip(mu, low, high, variance):
                if qh == ql:
                    continue
                if qv in (0, 1):
                    g = None
                    break
                g += w*(qh-ql)**2*((HALF+d)**k*(HALF-d)**(n-k)/qv
                                    +(HALF-d)**k*(HALF+d)**(n-k)/(1-qv))
            genie[n, k] = g
    return rewards, costs, genie


def priced_policy(rewards, costs, N, price, terminal=None):
    values = {}
    for n in range(N, 0, -1):
        for k in range(n+1):
            stop = rewards[n, k] if n < N or terminal is None else terminal[n, k]
            assert stop is not None
            if n == N:
                values[n, k] = (stop, F())
                continue
            il, cl = values[n+1, k]
            ir, cr = values[n+1, k+1]
            onward = il+ir, costs[n, k]+cl+cr
            values[n, k] = onward if onward[0]-price*onward[1] > stop else (stop, F())
    left, right = values[1, 0], values[1, 1]
    return left[0]+right[0], 1+left[1]+right[1]


def exact_ratio(rewards, costs, N, terminal=None):
    if any(rewards[n, k] is None for n in range(1, N+1) for k in range(n+1)):
        return None
    if terminal is not None and any(terminal[N, k] is None for k in range(N+1)):
        return None
    price = F()
    for _ in range(1000):
        information, work = priced_policy(rewards, costs, N, price, terminal)
        assert 1 <= work <= N
        if information == price*work:
            return price
        assert information > price*work
        price = information/work
    raise AssertionError('Exact finite policy iteration did not terminate')


def exhaustive_ordered_ratio(rewards, costs, N):
    internal = [x for n in range(1, N) for x in product((0, 1), repeat=n)]
    index = {x: i for i, x in enumerate(internal)}
    best = F()
    for mask in range(1 << len(internal)):
        def visit(x):
            n, k = len(x), sum(x)
            if n == N or not (mask >> index[x]) & 1:
                return rewards[n, k], F()
            il, cl = visit(x+(0,))
            ir, cr = visit(x+(1,))
            return il+ir, costs[n, k]+cl+cr
        il, cl = visit((0,))
        ir, cr = visit((1,))
        best = max(best, (il+ir)/(1+cl+cr))
    return best, 1 << len(internal)


def feasible_prior(rng, mu, rho, interior=False):
    q = [F(rng.randrange(0, 17), 16) for _ in mu]
    mass = expectation(mu, q)
    if mass > rho:
        q = [x*rho/mass for x in q]
    if interior:
        q = [(15*x+rho/2)/16 for x in q]
    assert all(0 <= x <= 1 for x in q) and expectation(mu, q) <= rho
    return q


def check_stopping_ratios():
    rng = random.Random(1616007)
    laws = [
        [(F(1, 2), F(1))],
        [(F(1, 2), F(1, 2)), (F(1, 4), F(1, 2))],
        [(F(3, 8), F(15, 16)), (F(1, 64), F(1, 16))],
        [(F(1, 2), F(1, 8)), (F(3, 16), F(3, 8)), (F(1, 16), F(1, 2))]
    ]
    trees = 0
    residual_checks = 0
    largest_residual_ratio = F()
    for trial in range(100):
        mu, rho = laws[trial % len(laws)], F(1, 8)
        quartet = [feasible_prior(rng, mu, rho, interior=i == 2) for i in range(4)]
        rewards, costs, genie = coefficients(mu, quartet, 6)
        prev_k, prev_plus = F(), None
        for N in range(1, 7):
            k = exact_ratio(rewards, costs, N)
            kp = exact_ratio(rewards, costs, N, genie)
            residual = genie[0, 0]-sum((comb(N, h)*rewards[N, h] for h in range(N+1)), F())
            assert prev_k <= k <= kp
            assert prev_plus is None or kp <= prev_plus
            assert 0 <= kp-k <= residual
            if residual:
                largest_residual_ratio = max(largest_residual_ratio, (kp-k)/residual)
            prev_k, prev_plus = k, kp
            residual_checks += 1
        N = 4 if trial < 2 else 3
        brute, count = exhaustive_ordered_ratio(rewards, costs, N)
        assert brute == exact_ratio(rewards, costs, N)
        trees += count
        low, high, var, work = quartet
        new_low = [(a+v+w)/3 for a, v, w in zip(low, var, work)]
        new_high = [(a+v+w)/3 for a, v, w in zip(high, var, work)]
        midpoint = [(a+b)/2 for a, b in zip(new_low, new_high)]
        rr, cc, _ = coefficients(mu, [new_low, new_high, midpoint, midpoint], 6)
        assert exact_ratio(rr, cc, 6) <= exact_ratio(rewards, costs, 6)
        assert expectation(mu, new_high)-expectation(mu, new_low) == (expectation(mu, high)-expectation(mu, low))/3
    # Singular reference and universally null count states are distinct cases.
    singular = coefficients(laws[0], [[F()], [F(1,8)], [F()], [F()]], 3)
    assert exact_ratio(singular[0], singular[1], 3) is None
    regular = coefficients(laws[0], [[F()], [F(1,8)], [F(1,8)], [F()]], 3)
    assert regular[0][2, 1] == 0
    assert exact_ratio(regular[0], regular[1], 3) == F(1, 7)
    return dict(quartets=100, ordered_stopping_trees_enumerated=trees,
                genie_monotonicity_and_residual_checks=residual_checks,
                absorption_checks=100, largest_genie_gap_over_residual=str(largest_residual_ratio),
                null_state_checks='singular reference -> infinity; universally null state -> zero')


def check_flows():
    rng = random.Random(1616011)
    count = 0
    for trial in range(120):
        N = 1+trial % 5
        states = [(n, k) for n in range(N+1) for k in range(n+1)]
        a, c, z, t = ({s: F() for s in states} for _ in range(4))
        ordered = {x: [F(), F(), F(), F()] for n in range(N+1) for x in product((0, 1), repeat=n)}
        for _ in range(4):
            def visit(x):
                n = len(x)
                if n == 0 or (n < N and rng.randrange(2)):
                    ordered[x][1] += F(1, 4)
                    visit(x+(0,)); visit(x+(1,))
                else:
                    y = F(rng.randrange(-12, 13), 3)
                    ordered[x][0] += F(1, 4)
                    ordered[x][2] += y/4
                    ordered[x][3] += y*y/4
            visit(())
        for x, values in ordered.items():
            s = len(x), sum(x)
            for target, value in zip((a, c, z, t), values):
                target[s] += value/comb(*s)
        assert c[0, 0] == 1 and a[0, 0] == z[0, 0] == t[0, 0] == 0
        for n, k in states[1:]:
            incoming = F(n-k, n)*c.get((n-1, k), F())+F(k, n)*c.get((n-1, k-1), F())
            assert a[n, k]+c[n, k] == incoming
            assert z[n, k]**2 <= a[n, k]*t[n, k]
        for p in (F(), F(1, 4), HALF, F(3, 4), F(1)):
            expected = [F(), F(), F()]
            for x, (_, co, zz, tt) in ordered.items():
                mass = p**sum(x)*(1-p)**(len(x)-sum(x))
                for j, value in enumerate((zz, tt, co)):
                    expected[j] += mass*value
            reach = {(0, 0): F(1)}
            realized = [F(), F(), F()]
            for n, k in states:
                reached = reach.get((n, k), F())
                total = a[n, k]+c[n, k]
                stopped = reached*a[n, k]/total if total else F()
                continued = reached-stopped
                output = z[n, k]/a[n, k] if a[n, k] else F()
                realized[0] += stopped*output
                realized[1] += stopped*output**2
                realized[2] += continued
                if n < N:
                    reach[n+1, k] = reach.get((n+1, k), F())+continued*(1-p)
                    reach[n+1, k+1] = reach.get((n+1, k+1), F())+continued*p
                else:
                    assert continued == 0
            assert realized[0] == expected[0]
            assert realized[1] <= expected[1]
            assert realized[2] == expected[2]
            count += 1
    return dict(randomized_order_dependent_policies=120, exact_conditional_realizations=count)


def check_one_atom_duality():
    count = 0
    for d, rho, B in product((F(1,2), F(3,8), F(1,8), F(1,128)),
                             (F(1,4), F(1,8), F(1,1024)),
                             (F(1,10000), F(1,2), F(1), F(100), F(1000000))):
        p = HALF-d+2*d*rho
        variance_coefficient = p*(1-p)/(4*d*d*B)
        bias_coefficient = rho*rho/4
        slope = bias_coefficient/(bias_coefficient+variance_coefficient)
        outputs = (-p*slope/(2*d*B), (1-p)*slope/(2*d*B))
        offset = rho*(1+slope)/2
        worst_bias = worst_variance = F()
        for q in (F(), rho):
            prob = HALF-d+2*d*q
            mean = offset+B*((1-prob)*outputs[0]+prob*outputs[1])
            variance = B*((1-prob)*outputs[0]**2+prob*outputs[1]**2)
            worst_bias = max(worst_bias, abs(mean-q))
            worst_variance = max(worst_variance, variance)
        primal = worst_bias**2+worst_variance
        K = (2*d*rho)**2/(p*(1-p))
        dual = rho*rho/(4+B*K)
        assert primal == dual
        count += 1
    return dict(exact_matching_primal_dual_witnesses=count,
                formula='P_1(B)^2 = rho^2 / (4 + B*(2*d*rho)^2/[p_rho*(1-p_rho)])')


def check_cap_arithmetic():
    count = 0
    for rho, B in product((F(1,4), F(1,8), F(1,1000)),
                           (F(1,1000000), F(1,10), F(1), F(4), F(8), F(100), F(300000))):
        N = ceil(64*max(B, rho*B*B))
        remainder_squared = rho*rho*B/(4*(N+1))
        floor_squared = min(rho*rho, rho/B)/256
        assert N >= 1 and remainder_squared <= floor_squared
        count += 1
    return dict(exact_budget_rarity_cases=count)


def fixed_cap_counterexample():
    mu = [(F(1,2), F(1,2)), (F(1,4), F(1,2))]
    rho, B, units = F(1,8), F(300000), 100000
    low, high = [F(1,8), F()], [F(), F(1,4)]
    for n in (1, 2):
        assert all(prefix(mu, low, n, k) == prefix(mu, high, n, k) for k in range(n+1))
    gap = expectation(mu, high)-expectation(mu, low)
    assert gap == F(1,16)
    # A genuine three-observation unbiased single-unit estimator.
    outputs = [F(), F(-5,9), F(14,9), F(1)]
    conditional_variances = []
    for d, _ in mu:
        vv = []
        for sign in (0, 1):
            p = HALF+(2*sign-1)*d
            masses = [F(comb(3, k))*p**k*(1-p)**(3-k) for k in range(4)]
            mean = sum((m*y for m, y in zip(masses, outputs)), F())
            variance = sum((m*y*y for m, y in zip(masses, outputs)), F())-mean**2
            assert mean == sign
            vv.append(variance)
        assert vv[0] == vv[1]
        conditional_variances.append(vv[0])
    risk_upper_squared = (sum((w*v for (_, w), v in zip(mu, conditional_variances)), F())
                          +rho*(1-rho))/units
    assert risk_upper_squared == F(203, 57600000)
    assert (gap/2)**2 > 256*risk_upper_squared
    # Exact finite-cap primal/dual optimum at this budget.
    pmax = F(1,4)
    outputs_one_flip = [-pmax/B, (1-pmax)/B]
    offset = F(5,32)
    vertices = [[F(), F()], [F(1,4), F()], [F(), F(1,4)]]
    bias, variance = F(), F()
    for q in vertices:
        p = prefix(mu, q, 1, 1)
        mean = offset+B*((1-p)*outputs_one_flip[0]+p*outputs_one_flip[1])
        bias = max(bias, abs(mean-expectation(mu, q)))
        variance = max(variance, B*((1-p)*outputs_one_flip[0]**2+p*outputs_one_flip[1]**2))
    exact_P1_squared = bias*bias+variance
    l = rho/2-F(3,2)/(B*rho)
    quartet = [[2*l, F()], high, [F(1,4), F()], [F(), F()]]
    reward, work, _ = coefficients(mu, quartet, 1)
    K = exact_ratio(reward, work, 1)
    delta = expectation(mu, quartet[1])-expectation(mu, quartet[0])
    assert exact_P1_squared == delta**2/(4+B*K) == F(1,1024)+F(3,16)/B
    G1_squared = rho*rho/(4+B*rho/(1-rho))
    assert exact_P1_squared > 4*G1_squared
    return dict(mu='(1/2) delta_(1/2) + (1/2) delta_(1/4)', rho=str(rho), budget=str(B),
                matching_pair={'low':list(map(str,low)), 'high':list(map(str,high))},
                cap_1_and_2_bias_floor=str(gap/2), exact_P1_squared=str(exact_P1_squared),
                unbiased_three_flip_outputs=list(map(str,outputs)), units=units,
                unrestricted_risk_upper_squared=str(risk_upper_squared),
                unrestricted_risk_upper=sqrt(float(risk_upper_squared)),
                P1_over_unrestricted_risk_lower=sqrt(float(exact_P1_squared/risk_upper_squared)),
                exact_G1_squared=str(G1_squared), P1_over_G1=sqrt(float(exact_P1_squared/G1_squared)),
                theoretical_N_star=ceil(64*max(B,rho*B*B)),
                interpretation='Refutes P_N <= 16 R at arbitrary fixed N. Does not refute the stated theorem: the genie criterion fails and N_star is much larger.')


def support(mu, rho, values):
    left, total = rho, F()
    for i in sorted(range(len(mu)), key=lambda i: values[i], reverse=True):
        if values[i] <= 0:
            break
        mass = min(left, mu[i][1])
        total += mass*values[i]
        left -= mass
    return total


def verify_stored_certificates():
    root = Path(__file__).resolve().parents[1] / 'tmp/astra-review-20261028/sources/adaptive_rare_event_estimation/checks'
    lower_count = upper_count = 0
    kinds = {}
    lower_results, upper_results = {}, {}
    for folder in ('certificates', 'genie_certificates', 'optimized_genie'):
        for path in sorted((root/folder).glob('*.json')):
            data = json.loads(path.read_text(encoding='utf-8'))
            if not isinstance(data, dict) or 'priors' not in data:
                continue
            mu = list(zip(map(F, data['gaps']), map(F, data['weights'])))
            rho, B, N = F(data['rho']), F(data['budget']), data['cap']
            quartet = [list(map(F, data['priors'][key])) for key in ('low', 'high', 'variance', 'work')]
            assert sum(w for _, w in mu) == 1 and all(w > 0 and 0 < d <= HALF for d, w in mu)
            assert 0 < rho <= F(1,4) and B > 0 and N >= 1
            for q in quartet:
                assert len(q) == len(mu) and all(0 <= x <= 1 for x in q)
                assert expectation(mu, q) <= rho
            reward, work, genie = coefficients(mu, quartet, N)
            kind = data.get('certificate_kind', 'finite_cap')
            price = F(data['information_work_price'])
            assert price >= 0
            info, cost = priced_policy(reward, work, N, price,
                                      genie if kind != 'finite_cap' else None)
            assert info <= price*cost
            gap = expectation(mu, quartet[1])-expectation(mu, quartet[0])
            assert gap >= 0
            if kind == 'uncapped_midpoint_genie':
                midpoint = [(a+b)/2 for a, b in zip(quartet[0], quartet[1])]
                assert quartet[2] == quartet[3] == midpoint
                x = B*price
                bound = gap*gap/4*(1-x/4)**2 if x <= F(4,3) else 4*gap*gap/(27*x)
            else:
                bound = gap*gap/(4+B*price)
            claim = F(data['certified_squared_lower_bound'])
            assert 0 <= claim <= bound
            assert 0 <= F(data['certified_rms_lower_bound_decimal'])**2 <= claim
            lower_results[path.stem] = claim
            kinds[kind] = kinds.get(kind, 0)+1
            lower_count += 1
    for path in sorted((root/'optimized_genie').glob('*_upper.json')):
        data = json.loads(path.read_text(encoding='utf-8'))
        mu = list(zip(map(F, data['gaps']), map(F, data['weights'])))
        rho, B, N = F(data['rho']), F(data['budget']), data['cap']
        intensity, offset = F(data['poisson_intensity']), F(data['offset'])
        states = [(n, k) for n in range(N+1) for k in range(n+1)]
        stop = dict(zip(states, map(F, data['stop_probability'])))
        output = dict(zip(states, map(F, data['terminal_output'])))
        assert stop[0, 0] == 0 and all(0 <= s <= 1 for s in stop.values())
        assert all(stop[N, k] == 1 for k in range(N+1))
        assert intensity >= 0
        by_sign = [[], []]
        # Backward conditional-moment evaluation, independent of the supplied
        # verifier's forward reach-probability calculation.
        for d, _ in mu:
            for sign in (0, 1):
                p = HALF+(2*sign-1)*d
                values = {}
                for n in range(N, -1, -1):
                    for k in range(n+1):
                        s, y = stop[n, k], output[n, k]
                        mean, second, work = s*y, s*y*y, 1-s
                        if n < N:
                            l, r = values[n+1, k], values[n+1, k+1]
                            mean += (1-s)*((1-p)*l[0]+p*r[0])
                            second += (1-s)*((1-p)*l[1]+p*r[1])
                            work += (1-s)*((1-p)*l[2]+p*r[2])
                        values[n, k] = mean, second, work
                by_sign[sign].append(values[0, 0])
        a, b = by_sign
        null_mean = offset+intensity*sum((w*x[0] for (_, w), x in zip(mu, a)), F())
        change = [intensity*(y[0]-x[0])-1 for x, y in zip(a, b)]
        bias = max(null_mean+support(mu, rho, change), -null_mean+support(mu, rho, [-x for x in change]))
        worst = []
        for j in (1, 2):
            worst.append(intensity*(sum((w*x[j] for (_, w), x in zip(mu, a)), F())
                                    +support(mu, rho, [y[j]-x[j] for x, y in zip(a, b)])))
        assert worst[1] <= B
        claim = F(data['certified_squared_upper_bound'])
        assert bias*bias+worst[0] <= claim
        assert F(data['certified_rms_upper_bound_decimal'])**2 >= claim
        upper_results[path.stem] = claim
        upper_count += 1
    passes, failures = [], []
    for name, upper in upper_results.items():
        lower = lower_results[name.replace('_upper', '_lower')]
        (passes if upper <= 4*lower else failures).append(name.replace('_upper', ''))
    assert len(passes) == 8 and len(failures) == 1
    return dict(lower_certificates=lower_count, upper_policies=upper_count, lower_scopes=kinds,
                factor_sixteen_stopping_passes=passes, factor_sixteen_stopping_failures=failures,
                method='Recomputed prefix Bellman values and backward policy moments; no manuscript verifier or solver imported.')


def main():
    report = {}
    for name, check in [('one_atom_duality', check_one_atom_duality),
                        ('flow_realization', check_flows),
                        ('stopping_ratios', check_stopping_ratios),
                        ('factor_sixteen_cap', check_cap_arithmetic),
                        ('fixed_cap_counterexample', fixed_cap_counterexample),
                        ('stored_certificates', verify_stored_certificates)]:
        report[name] = check()
        print('PASS', name, flush=True)
    report['status'] = 'PASS'
    report['scope'] = 'Exact finite checks and analytic witnesses; not a proof of the general compactness or adaptive comparison theorems.'
    dest = Path(__file__).with_name('finite_program_adversarial_audit_results.json')
    dest.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(dest, flush=True)


if __name__ == '__main__':
    main()
