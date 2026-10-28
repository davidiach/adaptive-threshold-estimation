"""Independent audit of weighted sign entropy and annular saturation.

Checks use exact rational arithmetic and explicit logarithm enclosures.
The counterexamples refute omissions of overlap weights, the minimum-mass
saturation term, or entropy-packing trimming. The manuscript retains all
three safeguards. No manuscript solver or verifier is imported.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import random


def log_interval(x, terms=50):
    x = F(x)
    assert x > 0
    power = 0
    while x < 1:
        x *= 2; power -= 1
    while x >= 2:
        x /= 2; power += 1
    def series(z):
        t = (z-1)/(z+1)
        low = 2*sum((t**(2*j+1)/(2*j+1) for j in range(terms)), F())
        error = 2*t**(2*terms+1)/((2*terms+1)*(1-t*t))
        return low, low+error
    lo, hi = series(x)
    l2, h2 = series(F(2))
    return (lo+power*l2, hi+power*h2) if power >= 0 else (lo+power*h2, hi+power*l2)


def check_constants():
    b0, kappa = F(1,1024), F(64,3)
    assert b0*kappa == F(1,48)
    assert F(1,48)/2 < F(1,8)**2  # Pinsker gives TV < 1/8.
    c_floor = F(8,5)/kappa
    assert c_floor == F(3,40) > F(1,16)
    event_mass_floor = 1-F(1,10)-(F(1,10)+F(1,8))-F(1,4)
    assert event_mass_floor == F(17,40) > F(1,4)
    l2, h2 = log_interval(2)
    assert 4+4*h2 < 8  # 4*(16 c + 1 + log 2) < 64 c + 8.
    assert b0/16 == F(1,4**7)
    overlap = 7+F(4,3)
    assert overlap == F(25,3)
    logzlo, logzhi = log_interval(overlap)
    logzlo += 8; logzhi += 8
    assert logzhi < 11
    assert 65+12/F(1,16) == 257
    sharper_lo = 65+(1+logzlo)/c_floor
    sharper_hi = 65+(1+logzhi)/c_floor
    assert sharper_hi < 214
    # Factor out exp(-28); all three branches dominate the printed constant.
    branches = {
        'large_information_product': F(2,3)/(256*kappa),
        'too_much_removed_mass': F(2,3)/576,
        'entropy_branch': F(2,3)/(1028*1040),
    }
    assert branches == {'large_information_product':F(1,8192),
                        'too_much_removed_mass':F(1,864),
                        'entropy_branch':F(1,1603680)}
    assert all(x >= F(1,2000000) for x in branches.values())
    return dict(weighted_constant=257, same_proof_also_implies_constant=214,
                sharper_coefficient_interval=[float(sharper_lo),float(sharper_hi)],
                actual_window_probability_lower=str(event_mass_floor),
                fair_weighted_overlap_bound=str(overlap),
                annular_branch_constants_after_factoring_exp_minus_28={k:str(v) for k,v in branches.items()})


def completely_overlapping_windows():
    rows = []
    for K in (1,2,4,8,16,32,64):
        gaps = [F(1,2**(j+7)) for j in range(K)]
        # Odd deterministic horizon; a majority decision has fair probability
        # exactly 1/2 for each output and endpoint error <= exp(-4)<1/10.
        horizon = 2/(gaps[-1]**2)+1
        assert horizon.denominator == 1 and horizon.numerator % 2 == 1
        ns = [F(1,1024)/(d*d) for d in gaps]
        assert all(n.denominator == 1 and n < horizon for n in ns)
        costs = [horizon*d*d for d in gaps]
        weighted_overlap = sum((1/(1+c) for c in costs),F())
        assert weighted_overlap < F(2,3) < F(25,3)
        _, logKhi = log_interval(K)
        mean_cost = sum(costs,F())/K
        assert 1+logKhi <= 257*mean_cost
        rows.append(dict(gaps=K, horizon=str(horizon),
                         unweighted_pathwise_overlap=K,
                         sum_fair_window_probabilities=str(F(K,2)),
                         weighted_pathwise_overlap=float(weighted_overlap)))
    return dict(construction='Fixed odd horizon N=2/d_min^2+1, output the majority sign. Every E_j is exactly the same minus-output event.',
                endpoint_error_certificate='Hoeffding <= exp(-4) < 1/10; exp(4)>1+4+8=13.',
                conclusion='Unweighted window disjointness fails arbitrarily badly. The manuscript weighted-overlap bound holds.',rows=rows)


def thin_annulus_counterexample():
    rho, mass, a, d = F(1,8), F(1,2048), F(1,128), F(1,2**64)
    y0, y1 = -(F(1,2)-a)/(2*a), (F(1,2)+a)/(2*a)
    assert (y0,y1) == (F(-63,2),F(65,2))
    for gap in (a,d):
        for sign in (0,1):
            p = F(1,2)+(2*sign-1)*gap
            mean = (1-p)*y0+p*y1
            expected = (1+(2*sign-1)*gap/a)/2
            assert mean == expected
            if gap == a:
                assert mean == sign
    bias = mass*(1-d/a)/2
    assert bias <= mass/2 < rho/64
    variance_upper = (y1-y0)**2/4
    assert variance_upper == 1024
    A = (1-mass)/a**2+mass/d**2
    # Gamma >= A. Since exp(1)<3, exp(-28)/(2e6)>1/(2e6*3^28).
    entropy_only_lower = rho*A/(2000000*3**28)
    assert entropy_only_lower > variance_upper
    saturation = mass/a**2
    assert saturation == 8
    assert rho*a*a*A > mass  # Even Gamma's lower bound fails activation.
    return dict(law='(1-1/2048) delta_(1/128) + (1/2048) delta_(2^-64)',
                rho=str(rho), one_flip_output=[str(y0),str(y1)],
                uniform_bias_bound=str(bias), allowed_bias=str(rho/64),
                null_work=1, uniform_variance_upper=str(variance_upper),
                rigorous_entropy_only_RHS_lower=float(entropy_only_lower),
                actual_saturation_term=str(saturation),
                conclusion='Dropping min{rho*Gamma, w_min/a^2} gives a false lower bound even with the printed tiny constant. The stated saturated bound is not contradicted.')


def trimming_counterexample():
    n, a = 64, F(1,128)
    endpoints = [a/F(4**j) for j in range(n)]
    norm = sum((b*b for b in endpoints),F())
    c = 1/norm
    weights = [c*b*b for b in endpoints]
    assert sum(weights,F()) == 1
    bmin = endpoints[-1]
    lnlo, lnhi = log_interval(n)
    Lnlo, Lnhi = 1+lnlo, 1+lnhi
    # Define lambda=bmin/(1+log n), rho=c*n*bmin^2/(1+log n).
    rholo, rhohi = c*n*bmin*bmin/Lnhi, c*n*bmin*bmin/Lnlo
    assert 0 < rholo <= rhohi < F(1,4)
    # With h=bmin/(2n), every complementary band takes ordinary work and
    # the outer rho cap is inactive. The all-retained set is truly optimal.
    assert Lnhi < 2*n
    comparisons = 0
    for removed in range(1,n+1):
        m = n-removed
        ordinary = F(4**removed-1,3)  # In units c*bmin; smallest r bands.
        if ordinary < n:
            assert m > 0
            lmlo,_ = log_interval(m)
            # Certifies sqrt(n*m*(1+log m)/(1+log n))+ordinary >= n.
            assert n*m*(1+lmlo) >= (n-ordinary)**2*Lnhi
        comparisons += 1
    geometric = sum((F(1,16**j) for j in range(n)),F())
    untrimmed_packed_ratio = 256*geometric/(n*n)
    untrimmed_entropy_over_saturation = n*n/(1024*geometric)
    assert untrimmed_packed_ratio < 1
    assert untrimmed_entropy_over_saturation > 1
    t, power = 0,1
    while power < n:
        t += 1; power *= 4
    m = n-t
    remaining_geometric = sum((F(1,16**j) for j in range(m)),F())
    # (1+log n)/(1+log m)>=1 gives this rational lower bound.
    trimmed_packed_ratio_lower = 256*remaining_geometric*16**t/(m*m)
    assert trimmed_packed_ratio_lower >= 1
    lmlo,lmhi = log_interval(m)
    entropy_retained_lower = m*(1+lmlo)/(n*Lnhi)
    assert entropy_retained_lower >= F(1,16)
    return dict(bands=n, equal_canonical_cost=True, lambda_definition='b_min/(1+log n)',
                rho_interval=[float(rholo),float(rhohi)],
                genuine_optimal_retained_set=True, removed_cardinalities_checked=comparisons,
                optimality_proof='For m retained bands, sqrt(n*m*(1+log m)/(1+log n)) >= m, since (1+log m)/m decreases for m>=1. Every removed band costs at least c*b_min.',
                untrimmed_actual_saturation_over_claimed_bound=float(untrimmed_packed_ratio),
                untrimmed_allocated_entropy_over_saturation=float(untrimmed_entropy_over_saturation),
                trimmed_bands=t, retained_bands=m,
                trimmed_actual_saturation_over_claimed_bound_lower=float(trimmed_packed_ratio_lower),
                entropy_fraction_retained_lower=float(entropy_retained_lower),
                conclusion='Even a genuinely optimal retained set can fail entropy-branch activation without trimming. The manuscript trimming restores the claimed margin.')


def normalization_checks():
    rng = random.Random(257288)
    for _ in range(500):
        tau = F(rng.randrange(1,100),100)
        band_mass = tau*F(rng.randrange(1,100),100)
        a = F(1,2**rng.randrange(2,20))
        gamma = tau/(a*a)*rng.randrange(1,100)
        theta = tau*F(rng.randrange(1,25),100)
        conditional = tau*tau*min((theta/tau)*(gamma/tau), (band_mass/tau)/(a*a))
        unnormalized = min(theta*gamma, tau*band_mass/(a*a))
        assert conditional == unnormalized
    return dict(exact_cases=500,
                identity='tau^2 min{(theta/tau)(Gamma/tau), (w_min/tau)/a^2} = min{theta Gamma, tau w_min/a^2}')


def main():
    report = {}
    for name,check in [('proof_constants',check_constants),
                       ('overlapping_windows',completely_overlapping_windows),
                       ('thin_annulus_counterexample',thin_annulus_counterexample),
                       ('trimming_counterexample',trimming_counterexample),
                       ('conditional_normalization',normalization_checks)]:
        report[name] = check()
        print('PASS',name,flush=True)
    report['status'] = 'PASS'
    report['scope'] = 'Exact proof-invariant checks and analytic counterexamples to omitted hypotheses/steps. No counterexample to the stated weighted-entropy or saturated-annular bounds was found.'
    dest = Path(__file__).with_name('sign_entropy_annular_audit_results.json')
    dest.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(dest,flush=True)


if __name__ == '__main__':
    main()
