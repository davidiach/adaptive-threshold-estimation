"""Independent adversarial checks of Section 3 / Appendix A.

No manuscript verifier is imported. Stopped-prefix and optimization checks
use exact rational arithmetic. Poisson allocation and mixed-kernel checks
are numerical falsification checks, not proofs of infinite-horizon bounds.
Run with Python 3; no third-party packages required.
"""
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
from functools import lru_cache
import json
import math
from pathlib import Path
import random


HALF = F(1, 2)
LN2_LO = 2 * sum((F(1, 3) ** (2*r+1) / (2*r+1) for r in range(24)), F())
LN2_HI = LN2_LO + 2 * F(1, 3)**49 / (49 * (1-F(1, 9)))


def support(mu, rho, base, increment):
    """Exact max of sum mu_i*(base_i+q_i*increment_i), 0<=q<=1, mu.q<=rho."""
    result = sum((w*x for (_, w), x in zip(mu, base)), F())
    left = rho
    for i in sorted(range(len(mu)), key=lambda i: increment[i], reverse=True):
        if increment[i] <= 0 or not left:
            break
        take = min(left, mu[i][1])
        result += take * increment[i]
        left -= take
    return result


def band(d):
    b = HALF
    while d <= b/2:
        b /= 2
    return b


def references(mu, selected):
    costs = {}
    for (d, _), weight in zip(mu, selected):
        if weight:
            b = band(d)
            costs[b] = costs.get(b, F()) + weight / d**2
    total = sum(costs.values(), F())
    return tuple((b, a/total) for b, a in costs.items())


def bank_table(mu, refs, rho, eps, horizon):
    table = {}
    for n in range(1, horizon+1):
        for k in range(n+1):
            negative = any((1-b)**k * (1+b)**(n-k) >= 1/(eps*pi)
                           for b, pi in refs)
            if negative:
                table[n, k] = 0
                continue
            null = sum((w*(HALF-d)**k*(HALF+d)**(n-k) for d, w in mu), F())
            alt = sum((pi*(HALF+b/4)**k*(HALF-b/4)**(n-k) for b, pi in refs), F())
            table[n, k] = 1 if not null or alt >= null/(rho*eps) else None
    return table


@lru_cache(None)
def ordinary_decision(M, n, k):
    if n == M:
        return int(2*k > n)
    if n & (n-1):
        return None
    power = (M//n).bit_length()-1
    squared = F((2*k-n)**2, 4*n)
    lo, hi = 1+power*LN2_LO, 1+power*LN2_HI
    assert not lo <= squared <= hi, "Increase logarithm enclosure precision"
    return int(2*k > n) if squared > hi else None


def stopped_law(p, horizon, decision):
    alive = {0: F(1)}
    survival = [F(1)]
    stops = [(F(), F())]
    for n in range(1, horizon+1):
        updated = {}
        for k, mass in alive.items():
            if p < 1:
                updated[k] = updated.get(k, F()) + mass*(1-p)
            if p:
                updated[k+1] = updated.get(k+1, F()) + mass*p
        alive = {}
        out = [F(), F()]
        for k, mass in updated.items():
            answer = decision(n, k)
            if answer is None:
                alive[k] = mass
            else:
                out[answer] += mass
        survival.append(sum(alive.values(), F()))
        stops.append(tuple(out))
    assert survival[-1] + sum((sum(x) for x in stops), F()) == 1
    return survival, stops


def race_law(bank, ordinary, M):
    sb, hb = bank
    so, ho = ordinary
    out = [F(), F()]
    for n in range(1, M+1):
        for answer in (0, 1):
            # Bank sees odd physical observations; an odd stop has priority.
            out[answer] += hb[n][answer]*so[n-1] + ho[n][answer]*sb[n]
    work = sum((so[n]*(sb[n]+sb[n+1]) for n in range(M)), F())
    assert sum(out) == 1
    assert work <= 2*sum(sb[:M])
    assert work <= 2*sum(so[:M])
    return out[1], work


def direct_race(p, table, M):
    """Independent physical-prefix DP; used to cross-check the factorization."""
    alive = {(0, 0): F(1)}
    out = [F(), F()]
    work = F()
    for t in range(1, 2*M+1):
        work += sum(alive.values(), F())
        updated = {}
        for (kb, ko), mass in alive.items():
            for bit, probability in ((0, 1-p), (1, p)):
                if not probability:
                    continue
                nb, no = kb+bit*(t % 2), ko+bit*(1-t % 2)
                answer = table[(t+1)//2, nb] if t % 2 else ordinary_decision(M, t//2, no)
                if answer is None:
                    updated[nb, no] = updated.get((nb, no), F()) + mass*probability
                else:
                    out[answer] += mass*probability
        alive = updated
    assert not alive and sum(out) == 1
    return out[1], work


def dec(x):
    return D(x.numerator)/D(x.denominator) if isinstance(x, F) else D(x)


def check_case(name, mu, selected, rho):
    refs = references(mu, selected)
    levels = []
    max_bank_fp_ratio = 0.
    max_bank_error_ratio = 0.
    max_truncated_bank_work_ratio = 0.
    max_ordinary_work_ratio = 0.
    exact_states = 0
    for ell, M in enumerate((4, 16, 64)):
        eps = F(1, 4**(ell+1))
        horizon = 96
        table = bank_table(mu, refs, rho, eps, horizon)
        outcomes = []
        bank_fp, bank_fn = [], []
        ordinary_errors = [[], []]
        for d, _ in mu:
            signs = []
            for sign in (0, 1):
                p = HALF+(2*sign-1)*d
                bank = stopped_law(p, horizon, lambda n, k: table[n, k])
                ordinary = stopped_law(p, M, lambda n, k: ordinary_decision(M, n, k))
                race = race_law(bank, ordinary, M)
                if M <= 16:
                    assert race == direct_race(p, table, M)
                ordinary_error = sum((x[1-sign] for x in ordinary[1]), F())
                assert ordinary_error <= min(1, 1/(M*d*d)**2)
                ordinary_work = sum(ordinary[0][:M])
                ordinary_bound = min(M, 17/float(d*d)*(1+max(0., math.log(float(M*d*d)))))
                assert float(ordinary_work) <= ordinary_bound*(1+1e-12)
                max_ordinary_work_ratio = max(max_ordinary_work_ratio, float(ordinary_work)/ordinary_bound)
                for b, pi in refs:
                    if b/2 < d <= b:
                        base = 1+math.log(float(1/eps))+math.log(float(1/pi))
                        if sign:
                            first_n = math.ceil(1/(d*d))
                            envelope = sum(float(w)*math.exp(-2*first_n*float(x*x)) for x, w in mu)
                            work_bound = 6/float(d*d)*(base+max(0., math.log(envelope/float(rho))))
                        else:
                            work_bound = .75/float(d*d)*base
                        truncated_work = float(sum(bank[0][:horizon]))
                        assert truncated_work <= work_bound*(1+1e-12)
                        max_truncated_bank_work_ratio = max(max_truncated_bank_work_ratio, truncated_work/work_bound)
                ordinary_errors[sign].append(ordinary_error)
                bank_error = sum((x[1-sign] for x in bank[1]), F())
                if sign:
                    bank_fn.append(bank_error)
                    assert bank_error <= eps
                else:
                    bank_fp.append(bank_error)
                assert (race[0] if sign == 0 else 1-race[0]) <= bank_error+ordinary_error
                signs.append(race)
                exact_states += horizon*(horizon+3)//2
            outcomes.append(signs)
        fp = sum((w*x for (_, w), x in zip(mu, bank_fp)), F())
        error = support(mu, rho, bank_fp, [b-a for a, b in zip(bank_fp, bank_fn)])
        assert fp <= rho*eps and error <= 2*rho*eps
        max_bank_fp_ratio = max(max_bank_fp_ratio, float(fp/(rho*eps)))
        max_bank_error_ratio = max(max_bank_error_ratio, float(error/(2*rho*eps)))
        race_fp = [o[0][0] for o in outcomes]
        race_fn = [1-o[1][0] for o in outcomes]
        race_work0 = [o[0][1] for o in outcomes]
        race_work_increment = [o[1][1]-o[0][1] for o in outcomes]
        error_bound = support(mu, rho, race_fp, [b-a for a, b in zip(race_fp, race_fn)])
        # Positive padding satisfies the lemma's v_l>0 hypothesis, including d=1/2.
        error_bound += F(1, 1024*4**ell)
        fp_bound = sum((w*x for (_, w), x in zip(mu, race_fp)), F())
        work_bound = support(mu, rho, race_work0, race_work_increment)
        levels.append((outcomes, error_bound, fp_bound, work_bound))

    qs = [tuple(F() for _ in mu)]
    for i, (_, w) in enumerate(mu):
        q = [F() for _ in mu]
        q[i] = min(1, rho/w)
        qs.append(tuple(q))
    qs.append(tuple(rho for _ in mu))
    v = [rho+levels[0][2]] + [levels[j][1]+levels[j-1][1] for j in (1, 2)]
    k = [levels[0][3]] + [levels[j][3]+levels[j-1][3] for j in (1, 2)]
    min_intensity, max_variance_ratio, checks = D('Infinity'), D(0), 0
    with localcontext() as ctx:
        ctx.prec = 70
        A = sum(((dec(a)*dec(b)).sqrt() for a, b in zip(v, k)), D(0))
        for q in qs:
            theta = sum((w*qi for (_, w), qi in zip(mu, q)), F())
            means, seconds, works = [], [], []
            for ell in range(3):
                mean = second = work = F()
                for i, ((_, w), qi) in enumerate(zip(mu, q)):
                    for sign, sign_mass in ((0, 1-qi), (1, qi)):
                        prob, cost = levels[ell][0][i][sign]
                        if ell:
                            prev, prev_cost = levels[ell-1][0][i][sign]
                            mark_mean = prob-prev
                            mark_second = prob+prev-2*prob*prev
                            mark_work = cost+prev_cost
                        else:
                            mark_mean, mark_second, mark_work = prob, prob, cost
                        mean += w*sign_mass*mark_mean
                        second += w*sign_mass*mark_second
                        work += w*sign_mass*mark_work
                assert second <= v[ell] and work <= k[ell]
                means.append(mean); seconds.append(second); works.append(work)
            bias = sum(means)-theta
            assert abs(bias) <= levels[-1][1]
            for B in map(D, ('0.00000001', '0.001', '1', '10000')):
                ns = [B/A*(dec(a)/dec(b)).sqrt() for a, b in zip(v, k)]
                actual_work = sum((n*dec(w) for n, w in zip(ns, works)), D(0))
                variance = sum((dec(s)/n for s, n in zip(seconds, ns)), D(0))
                bound = A*A/B
                assert actual_work <= B*(1+D('1e-60'))
                assert variance <= bound*(1+D('1e-60'))
                min_intensity = min(min_intensity, *ns)
                max_variance_ratio = max(max_variance_ratio, variance/bound)
                checks += 1
    return dict(name=name, conditional_prefix_state_visits=exact_states,
                bank_horizon=96, race_caps=[4, 16, 64],
                max_truncated_bank_fp_over_bound=max_bank_fp_ratio,
                max_truncated_bank_error_over_bound=max_bank_error_ratio,
                max_truncated_bank_work_over_bound=max_truncated_bank_work_ratio,
                max_ordinary_work_over_bound=max_ordinary_work_ratio,
                poisson_q_budget_checks=checks,
                minimum_poisson_mean=str(min_intensity),
                maximum_actual_variance_over_certificate=str(max_variance_ratio))


def eta(ds, ws, M):
    return sum(w*min(1., (M*d*d)**-2) for d, w in zip(ds, ws))


def ordinary_work(ds, ws, M):
    return sum(w*min(M, 17/d**2*(1+max(0., math.log(M*d*d)))) for d, w in zip(ds, ws))


def mixed_stress(trials=1500):
    rng = random.Random(319884)
    max_sum_ratio = max_kernel_ratio = max_mix_ratio = max_surcharge_ratio = 0.
    for trial in range(trials):
        count = rng.randrange(1, 13)
        ds = [2.**(-rng.randrange(1, 42))*rng.uniform(.51, 1) for _ in range(count)]
        if trial % 9 == 0:
            ds[0] = .5
        ws = [10.**rng.uniform(-12, 0) for _ in ds]
        ws = [w/sum(ws) for w in ws]
        rho = 2.**(-rng.randrange(2, 31))
        z = 0. if trial % 3 == 0 else rho*16.**(-rng.randrange(2, 10))*rng.uniform(.1, 1)
        sigma, tau = [], []
        for w in ws:
            fraction = rng.choice((0., 1., rng.random()))
            sigma.append((1-z)*w*fraction)
            tau.append((1-z)*w*(1-fraction))
        nu = [s+t for s, t in zip(sigma, tau)]
        A = sum(w/d**2 for d, w in zip(ds, sigma))
        H = sum(w/d for d, w in zip(ds, tau))
        band_cost = {}
        for d, w in zip(ds, sigma):
            if w:
                j = math.floor(-math.log2(d))
                band_cost[j] = band_cost.get(j, 0.)+w/d**2
        gamma = A+sum(a*math.log(A/a) for a in band_cost.values())
        # Maximize the surcharge over the global rarity constraint, allowing q=1
        # on an atom. The unresolved measure is z times the original atomic law.
        surcharge_per_positive_mass = [s/w/d**2*max(0., math.log((z+A*d*d+H*d)/rho))
                                       for d, w, s in zip(ds, ws, sigma)]
        left, surcharge = rho, 0.
        for i in sorted(range(count), key=lambda i: surcharge_per_positive_mass[i], reverse=True):
            take = min(left, ws[i])
            surcharge += take*surcharge_per_positive_mass[i]
            left -= take
        surcharge_bound = (math.log(3)+1/math.e)*A+H*H/(2*math.e*rho)
        assert surcharge <= surcharge_bound*(1+1e-12)
        if surcharge_bound:
            max_surcharge_ratio = max(max_surcharge_ratio, surcharge/surcharge_bound)
        if z:
            J = 0
            while rho*16.**(-(J+2)) >= 8*z:
                J += 1
        else:
            J = 8
        Ms, deltas, costs = [], [], []
        ordinary_sum = unresolved = 0.
        for ell in range(J+1):
            delta = rho*16.**(-(ell+1))
            M = 4
            while eta(ds, nu, M) > delta/8:
                M *= 4
            assert delta/128 < eta(ds, nu, M) <= delta/8
            assert not Ms or M > Ms[-1]
            if z:
                assert eta(ds, nu, M)+z <= delta/4
            O = ordinary_work(ds, tau, M)
            assert O <= 21*H*math.sqrt(M)*(1+1e-12)
            assert eta(ds, sigma, M) <= A/M*(1+1e-12)
            assert eta(ds, tau, M) <= H/math.sqrt(M)*(1+1e-12)
            ordinary_sum += math.sqrt(delta*O)
            unresolved += math.sqrt(z*delta*M)
            costs.append(80*(ell+1)*gamma+4*H*H/rho+2*O+2*z*M)
            deltas.append(delta); Ms.append(M)
        mix_bound = 3328*H+2*math.sqrt(21)*(H+math.sqrt(rho*A))
        assert ordinary_sum <= mix_bound*(1+1e-12)
        assert unresolved <= (math.sqrt(2*rho*A)+1024/(3*math.sqrt(8))*H)*(1+1e-12)
        if mix_bound:
            max_mix_ratio = max(max_mix_ratio, ordinary_sum/mix_bound)
        S = sum(math.sqrt(17*d*(costs[i]+(costs[i-1] if i else 0))) for i, d in enumerate(deltas))
        basis = math.sqrt(rho*gamma)+H
        assert S <= 33000*basis
        max_sum_ratio = max(max_sum_ratio, S/basis)
        if H:
            K = max(1, Ms[-1].bit_length()//2)
            kernel = sum(math.sqrt(eta(ds, tau, 4**k)*ordinary_work(ds, tau, 4**k)) for k in range(1, K+1))
            assert kernel <= 208*H*(1+1e-12)
            max_kernel_ratio = max(max_kernel_ratio, kernel/(208*H))
    return dict(trials=trials, random_seed=319884, maximum_S_over_cost_basis=max_sum_ratio,
                explicit_proven_constant_checked=33000, maximum_partial_kernel_over_208H=max_kernel_ratio,
                maximum_mixed_sum_over_bound=max_mix_ratio,
                maximum_globally_optimized_surcharge_over_bound=max_surcharge_ratio,
                scope='Floating-point falsification checks; finite partial kernel sums only.')


def main():
    cases = [
        ('perfect_observation_atom', [(F(1,2), F(1))], [F(1)], F(1,8)),
        ('selected_easy_hidden_hard', [(F(1,2), F(1,2)), (F(1,64), F(1,2))], [F(1,2), F()], F(1,8)),
        ('rare_hard_component', [(F(1,2), F(15,16)), (F(1,16), F(1,16))], [F(15,16), F(1,16)], F(1,16)),
        ('interior_and_boundary_gaps', [(F(5,16), F(1,4)), (F(1,4), F(1,4)), (F(1,8), F(1,4)), (F(3,64), F(1,4))], [F(1,8), F(1,4), F(1,16), F(1,4)], F(1,8)),
    ]
    results = []
    for args in cases:
        result = check_case(*args)
        results.append(result)
        print('PASS exact stopped-prefix and Poisson checks:', args[0], flush=True)
    stress = mixed_stress()
    print('PASS mixed-cap/kernel stress:', stress['trials'], flush=True)
    theta, n = F(1,8), F(1,100)
    shortcut_failures = {
        'selected_only_null_first_head_false_positive': str(F(1,2)*(HALF-F(1,64))),
        'fresh_coin_difference_second_moment_with_perfect_classifiers': str(2*theta*(1-theta)),
        'correct_compound_Poisson_variance_perfect_label': str(theta/n),
        'incorrect_centered_mark_variance': str(theta*(1-theta)/n),
        'note': 'These counterexamples concern alterations the manuscript explicitly avoids.'
    }
    report = dict(status='PASS', cases=results, mixed_stress=stress, shortcut_counterexamples=shortcut_failures,
                  limitations=['Finite bank horizons do not certify infinite-horizon error or work bounds.',
                               'Exact race tests use finite caps, not the large Section 3 cap schedule.',
                               'Infinite-horizon validity and the constant 33000 require analytic inequalities.'])
    destination = Path(__file__).with_name('upper_bound_adversarial_audit_results.json')
    destination.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(destination, flush=True)


if __name__ == '__main__':
    main()
