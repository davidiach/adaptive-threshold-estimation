"""Independent probes of B.3, C.4, and Section 4.4 (standard library only).

These checks are falsification attempts, not proofs of the general theorems.
Run with Python 3.11+. Prints a JSON audit record; imports no manuscript code.
"""
from fractions import Fraction as Q
from decimal import Decimal, localcontext
import json
import math
import random


def dec(x):
    if isinstance(x, Q):
        return Decimal(x.numerator) / Decimal(x.denominator)
    return Decimal(str(x))


def gate_probe():
    # A single known gap 1/4. SPRT walk stops at -1 or +50.
    # An independent 1/7 activation seed also exercises zero-work rejection.
    rho, activation, upper = Q(1, 10**22), Q(1, 7), 50
    pn, pp = Q(1, 4), Q(3, 4)

    def hit(p, state=0):
        if p == Q(1, 2):
            return Q(state + 1, upper + 1)
        r = (1 - p) / p
        return (1 - r ** (state + 1)) / (1 - r ** (upper + 1))

    beta, alpha = hit(pn), hit(pp)
    ym, yp = -beta / (alpha - beta), (1 - beta) / (alpha - beta)

    def original(p):
        prob = hit(p)
        mean = prob * yp + (1 - prob) * ym
        moment = (prob * yp**2 + (1 - prob) * ym**2) / activation
        work = activation * (1 - (upper + 1) * prob) / (1 - 2 * p)
        return mean, moment, work

    mn, vn, wn = original(pn)
    mp, vp, wp = original(pp)
    assert mn == 0 and mp == 1 and vp > vn
    moment = (1 - rho) * vn + rho * vp
    product = moment * wn

    def at_gate(p):
        live = {0: Q(1)}
        accepted = {}
        rejected = Q(0)
        rejected_work = Q(0)
        # G=min(16, first |S|>=4). At T=G the trial is accepted.
        for t in range(1, 17):
            nxt = {}
            for s, mass in live.items():
                for step, prob in ((1, p), (-1, 1-p)):
                    state, mass2 = s + step, mass * prob
                    if t == 16 or abs(state) == 4:
                        accepted[t,state] = accepted.get((t,state), Q(0)) + mass2
                    elif state == -1:
                        rejected += mass2
                        rejected_work += t*mass2
                    else:
                        nxt[state] = nxt.get(state, Q(0)) + mass2
            live = nxt
        assert not live and sum(accepted.values()) + rejected == 1
        pe = activation * sum(accepted.values())
        early_mean = sum(m * (hit(p, s)*yp + (1-hit(p, s))*ym)
                         for (t,s), m in accepted.items())
        second = sum(m * (hit(p, s)*yp**2 + (1-hit(p, s))*ym**2)
                     for (t,s), m in accepted.items()) / activation
        if p != Q(1,2):
            accepted_work = sum(m*(t + ((s+1)-(upper+1)*hit(p,s))/(1-2*p))
                                for (t,s), m in accepted.items())
            # Independently reconstruct the full trial cost from gate prefixes,
            # charging rejected prefixes and the accepted trial's remaining work.
            assert activation*(rejected_work+accepted_work) == original(p)[2]
        return pe, early_mean, second

    fair_prob = at_gate(Q(1, 2))[0]
    with localcontext() as ctx:
        ctx.prec = 70
        C, a, kappa = Decimal(7).exp(), Decimal(1)/4, Decimal(64)/3
        cg = 1 / (256*kappa*C**4)
        assert dec(product) >= dec(rho)/(64*a*a)
        assert a*a*dec(product) <= cg
        mz = C**3 * dec(fair_prob) * dec(moment)
        data = {}
        moments_z = []
        for name, p in (('negative', pn), ('positive', pp)):
            pe, ell, second = at_gate(p)
            zm = C*dec(fair_prob)*dec(ell/pe)
            z2 = C*C*dec(fair_prob)**2*dec(second/pe)
            moments_z.append(z2)
            work = original(p)[2] / pe
            # Renewal derivation: rejected trial work plus accepted trial work,
            # divided by acceptance probability, equals total trial work / pe.
            assert dec(fair_prob)/C <= dec(pe) <= C*dec(fair_prob)
            if name == 'negative':
                assert abs(zm) <= Decimal(1)/8
                assert z2 <= mz/dec(rho)
                null_work = work
            else:
                assert zm >= Decimal(1)/2
                assert z2 <= 3*mz/dec(rho)
            data[name] = {'acceptance_probability': str(pe),
                          'restarted_mean': str(zm),
                          'restarted_second_moment': str(z2),
                          'expected_restart_work': str(dec(work))}
        assert dec(rho)/16 <= mz <= 2*C**4*a*a*dec(product)
        assert mz*dec(null_work) <= C**4*dec(product)
        assert max(moments_z[0], (1-dec(rho))*moments_z[0]+dec(rho)*moments_z[1]) <= mz
        return {'rho': str(rho), 'gap': '1/4', 'seed_activation': str(activation),
                'upper_walk_boundary': upper, 'fair_acceptance_probability': str(fair_prob),
                'a_squared_P': str(a*a*dec(product)), 'c_g': str(cg),
                'necessary_local_rarity_for_small_branch': str(64*cg),
                'm_Z': str(mz), 'states': data, 'all_checks_passed': True}


def convex_compression_probe(trials=500, seed=20261029):
    # Exact rational checks of C.4's compression and shared-mixture variance.
    rng = random.Random(seed)
    def probvec(k):
        v = [rng.randint(1, 20) for _ in range(k)]
        return [Q(x, sum(v)) for x in v]
    def mv(p, values):
        m = sum(x*y for x,y in zip(p, values))
        return m, sum(x*y*y for x,y in zip(p, values)) - m*m
    largest_ratio = Q(0)
    for _ in range(trials):
        m, k, n = rng.randint(1, 5), rng.randint(2, 7), rng.randint(1, 7)
        weights, rho = probvec(m), Q(rng.randint(1, 25), 100)
        qm = [Q(rng.randint(0, 50), 100) for _ in range(m)]
        mass = sum(w*q for w,q in zip(weights,qm))
        if mass > rho:
            qm = [q*rho/mass for q in qm]
        theta = sum(w*q for w,q in zip(weights,qm))
        km, kp = [probvec(k) for _ in range(m)], [probvec(k) for _ in range(m)]
        p0 = [sum(weights[j]*km[j][i] for j in range(m)) for i in range(k)]
        pq = [sum(weights[j]*((1-qm[j])*km[j][i]+qm[j]*kp[j][i])
                  for j in range(m)) for i in range(k)]
        values = [[Q(rng.randint(-15,15), rng.randint(1,10)) for _ in range(k)]
                  for _ in range(n)]
        offset = Q(rng.randint(-10,10), 5)
        v0, vq = [mv(p0,v) for v in values], [mv(pq,v) for v in values]
        for (b,var0), (mean,varq) in zip(v0,vq):
            assert (mean-b)**2 <= 2*theta/(1-theta)*(var0+varq)
        f0, fq = offset+sum(x[0] for x in v0), offset+sum(x[0] for x in vq)
        r2 = max(sum(x[1] for x in v0)+f0*f0,
                 sum(x[1] for x in vq)+(fq-theta)**2)
        zm = z2 = Q(0)
        for i in range(n):
            for j in range(k):
                z = n*(values[i][j]-v0[i][0])+f0
                zm += pq[j]*z/n
                z2 += pq[j]*z*z/n
        vz = z2-zm*zm
        assert zm == fq
        assert vz <= Q(7,3)*n*r2
        if r2:
            largest_ratio = max(largest_ratio, vz/(n*r2))
    return {'trials': trials, 'seed': seed, 'arithmetic': 'exact Fraction',
            'largest_VarZ_over_n_r_squared': float(largest_ratio),
            'claimed_coefficient': 7/3, 'all_checks_passed': True}


def entropy(a):
    total = math.fsum(a)
    return math.fsum(x*(1+math.log(total/x)) for x in a) if total else 0.0


def packing_probe(trials=2000, seed=20261030):
    # Independent exhaustive finite selection, followed by the paper's packing.
    # Floating point is used here; ratios record slack, not exact certificates.
    rng = random.Random(seed)
    low_cases = groups = subsets = 0
    mins = {'retained_gap_ratio': float('inf'), 'entropy_tier_ratio': float('inf'),
            'trimmed_entropy_ratio': float('inf'), 'saturation_ratio': float('inf'),
            'retained_total_entropy_ratio': float('inf')}
    for trial in range(trials):
        m = rng.randint(1, 11)
        js = sorted(rng.sample(range(0, 121), m))
        bs = [2.0**(-j-1) for j in js]
        # Balanced cost, strongly unequal mass, and moderately unequal mass laws.
        mode = trial % 3
        ws = ([b*b*math.exp(rng.uniform(-.6,.6)) for b in bs] if mode==0 else
              [math.exp(rng.uniform(-90 if mode==1 else -8,0)) for _ in js])
        total = math.fsum(ws)
        ws = [w/total for w in ws]
        aa = [w/(b*b) for w,b in zip(ws,bs)]
        rho = math.exp(rng.uniform(-230, math.log(.25)))
        h = math.exp(rng.uniform(-350, 1))
        ordinary = [w*min(1,h/b) for w,b in zip(ws,bs)]
        best = None
        for mask in range(1<<m):
            chosen = [i for i in range(m) if mask>>i & 1]
            F = entropy([aa[i] for i in chosen])
            cost = h*math.sqrt(rho*F) + math.fsum(ordinary[i] for i in range(m)
                                                if not (mask>>i & 1))
            if best is None or cost < best[0]:
                best = (cost, chosen, F)
        subsets += 1<<m
        _, chosen, F = best
        if not chosen:
            continue
        lam, A = math.sqrt(rho/F), math.fsum(aa[i] for i in chosen)
        for i in chosen:
            rhs = lam/2*(1+math.log(A/aa[i]))
            ratio = bs[i]/rhs
            # Float selection can lose negligible mass changes at extreme scales.
            if ratio < 1-1e-8:
                raise AssertionError(('retained inequality', trial, js, ws, rho,h,chosen,ratio))
            mins['retained_gap_ratio'] = min(mins['retained_gap_ratio'], ratio)
        low = [i for i in chosen if js[i]>=6]
        if not low:
            continue
        low_cases += 1
        F_low = entropy([aa[i] for i in low])
        retained_entropies = []
        for parity in (0,1):
            indices = [i for i in low if js[i]%2==parity]
            if not indices:
                continue
            maxa = max(aa[i] for i in indices)
            tiers = {}
            for i in indices:
                tier = math.floor(math.log2(maxa/aa[i]))
                tiers.setdefault(tier, []).append(i)
            group_costs = [entropy([aa[i] for i in v]) for v in tiers.values()]
            tier_ratio = 7*math.fsum(group_costs)/entropy([aa[i] for i in indices])
            assert tier_ratio >= 1-1e-10
            mins['entropy_tier_ratio'] = min(mins['entropy_tier_ratio'], tier_ratio)
            for ids in tiers.values():
                groups += 1
                n = len(ids)
                remove = math.ceil(math.log(n,4)) if n>1 else 0
                keep = sorted(ids, key=lambda i:bs[i], reverse=True)[:n-remove]
                G = entropy([aa[i] for i in keep])
                ratio = 16*G/entropy([aa[i] for i in ids])
                assert ratio >= 1-1e-10
                mins['trimmed_entropy_ratio'] = min(mins['trimmed_entropy_ratio'], ratio)
                tau = math.fsum(ws[i] for i in keep)
                wmin, amax = min(ws[i] for i in keep), max(bs[i] for i in keep)
                saturation = tau*wmin/(amax*amax)
                ratio = saturation/(lam*lam*G*G/256)
                assert ratio >= 1-1e-8
                mins['saturation_ratio'] = min(mins['saturation_ratio'], ratio)
                theta = lam*lam*G/1024
                assert theta <= wmin/4*(1+1e-8)
                assert theta*G <= saturation/4*(1+1e-8)
                retained_entropies.append(G)
        ratio = math.fsum(retained_entropies)*224/F_low
        assert ratio >= 1-1e-10
        assert lam*lam*math.fsum(retained_entropies)/1024 <= rho/1024*(1+1e-10)
        mins['retained_total_entropy_ratio'] = min(mins['retained_total_entropy_ratio'], ratio)
    return {'laws': trials, 'seed': seed, 'subsets_enumerated': subsets,
            'laws_with_retained_low_bands': low_cases, 'groups_checked': groups,
            'minimum_LHS_over_RHS': mins, 'arithmetic': 'floating point; tolerance 1e-8',
            'all_checks_passed': True}


if __name__ == '__main__':
    print(json.dumps({'gate':gate_probe(), 'compression':convex_compression_probe(),
                      'packing':packing_probe()}, indent=2))
