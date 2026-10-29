"""Independent integration checks for the entropy--tail main theorem.

These are floating-point falsification tests, not proofs. The analytic
constant calculation and infinite-tail examples are recorded separately.
No manuscript implementation is imported. Original source is not modified.
"""
import json
import math
import random
from pathlib import Path
from decimal import Decimal, getcontext
from functools import lru_cache
from fractions import Fraction

getcontext().prec = 120


@lru_cache(maxsize=None)
def precise_items(items):
    return tuple((j, Decimal.from_float(d), Decimal.from_float(w)) for j,d,w in items)


@lru_cache(maxsize=None)
def precise_entropy(items, mask):
    costs = {}
    for i,(j,d,w) in enumerate(precise_items(items)):
        if mask >> i & 1:
            costs[j] = costs.get(j,Decimal(0)) + w/d**2
    A = sum(costs.values(), Decimal(0))
    F = A + sum((x*(A/x).ln() for x in costs.values()), Decimal(0)) if A else Decimal(0)
    return F, F.sqrt()

ANN = math.exp(-28) / 2_000_000
SEED = 2026102809


def entropy(a):
    a = [x for x in a if x > 0]
    A = math.fsum(a)
    return A + math.fsum(x * math.log(A / x) for x in a) if A else 0.0


def grouped(mu):
    result = {}
    for j, d, w in mu:
        result[j] = result.get(j, 0.0) + w
    return [(j, 2.0 ** (-j-1), w) for j, w in sorted(result.items())]


def optimize(mu, rho, h, canonical=False):
    items = grouped(mu) if canonical else mu
    n = len(items)
    candidates = []
    for mask in range(1 << n):
        costs = {}
        ordinary = 0.0
        for i, (j, d, w) in enumerate(items):
            if mask >> i & 1:
                costs[j] = costs.get(j, 0.0) + w / d**2
            else:
                ordinary += w * min(1.0, h / d)
        F = entropy(costs.values())
        value = h * math.sqrt(rho * F) + ordinary
        candidates.append((value, mask, F))
    approximate = min(candidates)[0]
    near = [x for x in candidates if x[0] <= approximate * (1+1e-12)]
    if len(near) > 1:
        key = tuple(items)
        dh, dr = Decimal.from_float(h), Decimal.from_float(rho)
        precise = []
        for _, trial_mask, _ in near:
            DF, rootF = precise_entropy(key,trial_mask)
            tail = sum((w*min(Decimal(1),dh/d) for i,(_,d,w) in enumerate(precise_items(key))
                        if not trial_mask >> i & 1), Decimal(0))
            precise.append((dh*dr.sqrt()*rootF+tail, trial_mask, DF))
        value, mask, F = min(precise)
        value, F = float(value), float(F)
    else:
        value, mask, F = min(candidates)
    return min(rho, value), value, mask, F, items


def psi(mu, rho, h):
    # Exact water filling up to floating-point arithmetic; no optimization solver.
    active = sorted(mu, key=lambda t: t[1])
    saturated = []
    remaining = rho
    while True:
        denominator = math.fsum(w / d**2 for _, d, w in active)
        alpha2 = remaining / denominator
        # If the first atom consumes the whole remaining budget, the true
        # root is below its saturation threshold. Very separated gaps can
        # round this strict inequality to equality in binary64 arithmetic.
        if alpha2 < active[0][1]**2 or remaining <= active[0][2]:
            break
        j, d, w = active.pop(0)
        saturated.append((j, d, w))
        remaining -= w
        assert active and remaining > 0
    alpha = math.sqrt(alpha2)
    if h >= alpha:
        return rho
    return math.fsum(w * min(1.0, h / d) for _, d, w in saturated) + math.fsum(
        w * h * alpha / d**2 for _, d, w in active)


def lower_chain(mu, rho, h, canonical_result, p):
    k, inner, mask, F, items = canonical_result
    selected = [x for i, x in enumerate(items) if mask >> i & 1]
    ordinary = [x for i, x in enumerate(items) if not mask >> i & 1 and x[1] >= h]
    ignored = [x for i, x in enumerate(items) if not mask >> i & 1 and x[1] < h]
    H = math.fsum(w / d for _, d, w in ordinary)
    z = math.fsum(w for _, _, w in ignored)
    assert min(rho, z) <= p * (1 + 1e-9)
    assert h * H <= 2 * p * (1 + 1e-8)
    assert all(w <= rho * (1 + 1e-8) for _, _, w in ordinary), (mu, rho, h, canonical_result, ordinary)
    base = p / 8192
    if not selected:
        return base, {'branch': 'no_retained', 'components': 0, 'z': z}
    A = math.fsum(w / d**2 for _, d, w in selected)
    for _, d, w in selected:
        assert d >= math.sqrt(rho / F) / 2 * (1 + math.log(A / (w/d**2))) * (1 - 1e-8)
    Fhigh = entropy([w / d**2 for j, d, w in selected if j < 6])
    Flow = entropy([w / d**2 for j, d, w in selected if j >= 6])
    assert F <= 2 * (Fhigh + Flow) * (1 + 1e-9)
    if Fhigh >= Flow:
        assert min(rho, h * math.sqrt(rho * F)) <= 112 * p * (1 + 1e-9)
        return base, {'branch': 'high', 'components': 0, 'z': z}
    components = []
    for parity in (0, 1):
        part = [x for x in selected if x[0] >= 6 and x[0] % 2 == parity]
        if not part:
            continue
        M = max(w/d**2 for _, d, w in part)
        tiers = {}
        for x in part:
            _, d, w = x
            key = math.floor(math.log2(M / (w / d**2)))
            tiers.setdefault(key, []).append(x)
        for group in tiers.values():
            n = len(group)
            t = 0
            while 4**t < n:
                t += 1
            keep = sorted(group, key=lambda x: x[1], reverse=True)[:n-t]
            G = entropy([w/d**2 for _, d, w in keep])
            tau = math.fsum(w for _, _, w in keep)
            endpoint = max(d for _, d, _ in keep)
            wmin = min(w for _, _, w in keep)
            theta = rho * (G / F) / 1024
            saturation = tau * wmin / endpoint**2
            assert theta * G <= saturation / 4 * (1 + 1e-8)
            assert theta <= tau / 4 * (1 + 1e-8)
            components.append((G, tau, theta, saturation))
    Gsum = math.fsum(x[0] for x in components)
    assert Gsum >= F / 896 * (1 - 1e-8)
    assert math.fsum(x[2] for x in components) <= rho / 1024 * (1 + 1e-8)
    localized = math.fsum(min(theta / 64, h * math.sqrt(ANN * min(theta*G, sat)))
                         for G, tau, theta, sat in components) / 128
    exact_common = Gsum / 128 * min(rho / (F * 65536), h * math.sqrt(ANN * rho / F) / 32)
    assert math.isclose(localized, exact_common, rel_tol=1e-9)
    return max(base, localized), {'branch': 'packed', 'components': len(components), 'z': z}


def upper_chain(mu, rho, h, exact_result):
    K, inner, mask, G, items = exact_result
    if inner >= rho:
        return rho / 2, {'branch': 'outer_cap', 'levels': 0}
    sigma = [x for i, x in enumerate(items) if mask >> i & 1]
    tau = [x for i, x in enumerate(items) if not mask >> i & 1 and x[1] >= h]
    z = math.fsum(w for i, (_, d, w) in enumerate(items) if not mask >> i & 1 and d < h)
    if z > rho / 128:
        return rho / 2, {'branch': 'large_ignored', 'levels': 0}
    H = math.fsum(w/d for _, d, w in tau)
    basis = math.sqrt(rho * G) + H
    assert basis > 0
    if z:
        J = 0
        while rho * 16.0 ** (-J-2) >= 8*z:
            J += 1
    else:
        J = 0
        while rho * 16.0 ** (-J-1) > inner * 1e-4:
            J += 1
    resolved = sigma + tau
    S = 0.0
    prev_C = 0.0
    prev_cap = 0
    for ell in range(J+1):
        delta = rho * 16.0 ** (-ell-1)
        cap_power = 1
        def eta(M):
            return math.fsum(w * min(1.0, (M*d*d)**-2) for _, d, w in resolved)
        while eta(4.0 ** cap_power) > delta / 8:
            cap_power += 1
        M = 4.0 ** cap_power
        assert M > prev_cap
        assert delta / 128 < eta(M) * (1 + 1e-9)
        O = math.fsum(w * min(M, 17/d**2 * (1 + max(0.0, math.log(M*d*d)))) for _, d, w in tau)
        C = 80 * (ell+1) * G + 4 * H**2 / rho + 2 * O + 2 * z * M
        S += math.sqrt(17 * delta * (C + prev_C))
        prev_C = C
        prev_cap = M
    assert S <= 33000 * basis * (1 + 1e-9)
    U = min(rho/2, math.hypot(delta, S*h))
    return U, {'branch': 'finite_poisson', 'levels': J+1, 'S_over_basis': S / basis,
               'ignored_positive': z > 0}


def random_laws(count):
    rng = random.Random(SEED)
    laws = []
    for index in range(count):
        n = rng.randint(1, 9)
        js = sorted(rng.choices(range(0, 81), k=n))
        ds = [2.0**(-j-1) * rng.choice([1.0, 0.5001, 0.6, 0.9]) for j in js]
        mode = index % 4
        raw = ([1.0] * n if mode == 0 else
               [d*d for d in ds] if mode == 1 else
               [d*d*math.exp(rng.uniform(-.6,.6)) for d in ds] if mode == 2 else
               [math.exp(rng.uniform(-70,0)) for _ in ds])
        total = math.fsum(raw)
        laws.append([(j,d,w/total) for j,d,w in zip(js,ds,raw)])
    return laws


def structured_stress():
    # For every n>=2 this is an analytically certified all-retained optimum.
    # b_j=2^-7*4^-j, w_j=c*b_j^2, rho=c*n*b_min^2/(1+log n),
    # h=b_min/[10*(1+log n)]. Then K=rho/10 and K/Psi=sqrt(1+log n).
    rows = []
    for n in (4,16,64,256,1024):
        dn = Decimal(n)
        ell = 1+dn.ln()
        bmin = Decimal(2)**(-7) * Decimal(4)**(-(n-1))
        c = (Decimal(15)/16) / (Decimal(2)**(-14) * (1-Decimal(16)**(-n)))
        rho = c*dn*bmin**2/ell
        F = c*dn*ell
        h = bmin/(10*ell)
        K = h*(rho*F).sqrt()
        p = h*(rho*c*dn).sqrt()
        assert abs(K/(rho/10)-1) < Decimal('1e-110')
        t = 0
        while 4**t<n:
            t+=1
        m = n-t
        G = c*m*(1+Decimal(m).ln())
        tau = (1-Decimal(16)**(-m))/(1-Decimal(16)**(-n))
        wmin = c*(Decimal(2)**(-7)*Decimal(4)**(-(m-1)))**2
        sat = tau*wmin/(Decimal(2)**(-14))
        theta = rho*G/F/1024
        assert theta*G <= sat/4
        assert G >= F/16
        rows.append({'bands':n,'log10_rho':float(rho.log10()),'K_over_Psi':float(K/p),
                     'trimmed_bands':t,'retained_entropy_fraction':float(G/F),
                     'allocated_entropy_over_saturation':float(theta*G/sat)})
    # No law-uniform finite-prefix cutoff: full K=rho while k_0 is tiny.
    rho = Fraction(1,8)
    B = 2**80
    mu = [(0,.5,7/8),(99,2.0**-100,1/8)]
    full = optimize(mu,float(rho),2.0**-40)[0]
    prefix = 2.0**-40*math.sqrt(7)/4
    assert full == float(rho)
    # An infinite probability law with both inverse moments infinite.
    tail_rows = []
    for J in (8,32,128,512):
        h = Fraction(1,2**J)
        z = Fraction(1,J+1)
        ordinary = sum((h*2**j/Fraction(j*(j+1)) for j in range(1,J+1)),Fraction(0))
        upper_K = z+ordinary
        lower_Psi = min(Fraction(1,8),z)
        assert upper_K <= z+Fraction(8,J*J)+Fraction(1,2**(J//2))
        tail_rows.append({'log2_budget':2*J,'ignored_mass':float(z),
                          'K_upper':float(upper_K),'Psi_lower':float(lower_Psi),
                          'K_upper_over_Psi_lower':float(upper_K/lower_Psi)})
    return {'many_band_family':{'formula':'K/Psi=sqrt(1+log n), with a genuine all-retained optimum; no uniform Psi-only replacement is possible.',
                              'rows':rows},
            'nonuniform_prefix_example':{'law':'(7/8) delta_(1/2)+(1/8) delta_(2^-100)',
                'rho':'1/8','B':str(B),'full_K':full,'one_band_prefix_k':prefix,
                'full_over_prefix':full/prefix,'status':'The manuscript tail-mass remainder protects its limit argument.'},
            'infinite_moment_example':{'law':'mass 1/[j(j+1)] at d=2^-j, j>=1',
                'inverse_first_moment':'infinite','inverse_second_moment':'infinite',
                'conclusion':'At B=4^J and fixed rho=1/8, the explicit upper functional and ignored-tail lower modulus both have order 1/J.',
                'rows':tail_rows}}


def run():
    rng = random.Random(SEED+1)
    laws = random_laws(320)
    laws += [[(0, .5, 1.0)], [(0,.5,1-2**-10), (39,2**-40,2**-10)]]
    laws += [[(j,2.0**(-j-1), 1/n) for j in range(n)] for n in (2,6,9)]
    stats = {'laws':len(laws), 'inputs':0, 'upper_branches':{}, 'lower_branches':{},
             'max_exact_over_canonical':0.0, 'max_upper_over_K':0.0,
             'min_lower_over_K':float('inf'), 'max_S_over_basis':0.0,
             'packed_components':0, 'max_levels':0, 'mixed_three_piece_inputs':0}
    witness = {}
    for law_index, mu in enumerate(laws):
        for it in range(16):
            rho = [0.25,2**-10,2**-40,2**-100][it%4]
            if it < 4:
                h = [4.0, 1.0, 0.5, math.sqrt(rho)][it]
            elif it < 8:
                h = rng.choice(mu)[1] * [0.49, 0.99, 1.0, 1.01][it-4]
            else:
                h = 2.0**rng.uniform(-150, 0)
            exact = optimize(mu,rho,h)
            canonical = optimize(mu,rho,h,True)
            K, k = exact[0], canonical[0]
            assert k <= K*(1+1e-8) and K <= 2*k*(1+1e-8)
            floor = min(rho,2*h*math.sqrt(rho))
            assert K >= floor*(1-1e-8)
            if h >= math.sqrt(rho)/2:
                assert math.isclose(K,rho,rel_tol=1e-8)
            p = psi(mu,rho,h)
            L, lo = lower_chain(mu,rho,h,canonical,p)
            U, up = upper_chain(mu,rho,h,exact)
            assert L <= U*(1+1e-8)
            assert L >= 1e-17*K and U <= 33000*K
            stats['inputs'] += 1
            for key, branch in [('upper_branches',up['branch']),('lower_branches',lo['branch'])]:
                stats[key][branch] = stats[key].get(branch,0)+1
            stats['packed_components'] += lo['components']
            stats['max_levels'] = max(stats['max_levels'],up['levels'])
            stats['max_S_over_basis'] = max(stats['max_S_over_basis'],up.get('S_over_basis',0))
            if up.get('ignored_positive'):
                stats['mixed_three_piece_inputs'] += 1
            for key, value, bigger in [('max_exact_over_canonical', K/k, True),
                                       ('max_upper_over_K',U/K,True),('min_lower_over_K',L/K,False)]:
                if (value > stats[key]) if bigger else (value < stats[key]):
                    stats[key] = value
                    witness[key] = {'law_index':law_index,'law':mu,'rho':rho,'h':h,
                                    'K':K,'canonical_k':k,'Psi':p,'lower':L,'upper':U,
                                    'upper_detail':up,'lower_detail':lo}
    root_ann = math.sqrt(ANN)
    c_ret = root_ann / (896*128*32)
    c_main = 1 / (2*(81920+1/c_ret))
    c_sum_gamma = 5*math.sqrt(17)/4 * (4*math.sqrt(80)/9+2*math.sqrt(42)+2)
    c_sum_H = 5*math.sqrt(17)/4 * (2/3+math.sqrt(2)*(3328+2*math.sqrt(21))+512/3)
    assert c_main > 1e-17 and max(c_sum_gamma,c_sum_H,128) < 33000
    # Rational bounds certify the displayed round constants independently
    # of transcendental floating-point evaluations. Use e<3, sqrt(2e6)<1500;
    # sqrt(17)<33/8, sqrt(2)<3/2, sqrt(21)<5, sqrt(42)<7, sqrt(80)<9.
    lower_denominator_bound = 2*(81920 + 896*128*32*1500*3**14)
    assert lower_denominator_bound < 10**17
    upper_entropy_bound = Fraction(165,32)*20
    upper_ordinary_bound = Fraction(165,32)*(Fraction(514,3)+Fraction(3,2)*(3328+10))
    assert max(upper_entropy_bound,upper_ordinary_bound,128) < 33000
    output = {'status':'PASS','arithmetic':'Floating point with 120-digit Decimal tie resolution for subset optimization; structured families also use exact rational calculations. All claims about every input require the analytic argument.',
              'seed':SEED,'integration_checks':stats,'extremal_witnesses':witness,
              'explicit_constants':{'annular':ANN,'retained_lower':c_ret,'main_lower':c_main,
                  'upper_entropy_coefficient':c_sum_gamma,'upper_ordinary_coefficient':c_sum_H,
                  'rational_lower_denominator_bound':str(lower_denominator_bound),
                  'rational_upper_entropy_bound':str(upper_entropy_bound),
                  'rational_upper_ordinary_bound':str(upper_ordinary_bound),
                  'safe_main_comparison':[1e-17,33000]},
              'structured_stress':structured_stress(),
              'scope':'Optimized exact and canonical selections, variational ordinary/ignored bounds, full conditional normalization and saturation, additive lower sum, and actual finite cap/Poisson certificates on the same inputs.'}
    target = Path(__file__).with_name('main_theorem_integration_audit_results.json')
    target.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],**stats,'constants':output['explicit_constants']},indent=2))


if __name__ == '__main__':
    run()
