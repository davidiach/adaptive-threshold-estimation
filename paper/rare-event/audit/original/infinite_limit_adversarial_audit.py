"""Independent audit of infinite-cap/genie limits and identification.

The continuous-law counterexample is exact: mu(dd)=2 dd on (0,1/2],
rho=1/4, q_L=0, q_H=q_w=1/4, q_v(d)=1/2-d. Its latent divergence
is infinite, so K_N^+=infinity at every finite N. Nevertheless, K_infinity
<=3/4, proved by the stopped-prefix inequality recorded below.

This refutes unconditional pointwise genie convergence, not the manuscript's
optimized convergence after regularizing the variance reference.
No manuscript solver or verifier is imported. All finite decisions use
Fraction arithmetic; logarithms have explicit rational enclosures.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json
import random


def solve(matrix, rhs):
    n = len(rhs)
    a = [list(row)+[b] for row, b in zip(matrix, rhs)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if a[i][col])
        a[col], a[pivot] = a[pivot], a[col]
        value = a[col][col]
        a[col] = [x/value for x in a[col]]
        for i in range(n):
            if i != col:
                value = a[i][col]
                a[i] = [x-value*y for x, y in zip(a[i], a[col])]
    return [row[-1] for row in a]


def log_enclosure(x, terms=60):
    """Rigorous natural-log interval, using range reduction and atanh series."""
    assert x > 0
    shift = 0
    while x < 1:
        x *= 2; shift -= 1
    while x >= 2:
        x /= 2; shift += 1
    def reduced(z):
        y = (z-1)/(z+1)
        lower = 2*sum((y**(2*j+1)/(2*j+1) for j in range(terms)), F())
        error = 2*y**(2*terms+1)/((2*terms+1)*(1-y*y))
        return lower, lower+error
    a, b = reduced(x)
    l2, u2 = reduced(F(2))
    if shift >= 0:
        return a+shift*l2, b+shift*u2
    return a+shift*u2, b+shift*l2


def coefficients(cap, epsilon=F()):
    """Closed-form ordered-prefix kernels for the continuous counterexample.

    U is the auxiliary uniform law of Bernoulli mean p. Its q=1/2 is not
    admissible; it is used only as a dominating measure in the proof.
    Under q_v, p has Beta(1,2) density 2(1-p).
    Under q_w, p has density 3/2 below 1/2 and 1/2 above 1/2.
    """
    reward, work, uniform, variance = {}, {}, {}, {}
    for n in range(cap+1):
        cumulative = 0
        for k in range(n+1):
            u = F(1, (n+1)*comb(n, k))
            cumulative += comb(n+1, k)
            a = F(2*cumulative, 2**(n+1))-1
            contrast = u*a/2
            old_v = F(2*(n-k+1), n+2)*u
            midpoint_v = u*(1-F(3,4)*a)
            v = (1-epsilon)*old_v+epsilon*midpoint_v
            w = u*(1-a/2)
            reward[n, k] = contrast*contrast/v
            work[n, k], uniform[n, k], variance[n, k] = w, u, v
            assert w >= u/2
            if n:
                # The analytic inequality holds for EVERY n,k. Summing it
                # against stopped-prefix seed weights gives I <= (3/8) E_U T.
                old_r = contrast*contrast/old_v
                assert old_r <= F(n+2, 8*(n-k+1))*u <= F(3*n,8)*u
                assert reward[n, k] <= old_r/(1-epsilon)
    return reward, work, uniform, variance


def ratio(reward, work, cap):
    price = F()
    for iteration in range(1000):
        values = {}
        for n in range(cap, 0, -1):
            for k in range(n+1):
                stop = reward[n, k], F()
                if n == cap:
                    values[n, k] = stop
                else:
                    left, right = values[n+1, k], values[n+1, k+1]
                    onward = left[0]+right[0], work[n, k]+left[1]+right[1]
                    values[n, k] = onward if onward[0]-price*onward[1] > stop[0] else stop
        left, right = values[1, 0], values[1, 1]
        info, cost = left[0]+right[0], 1+left[1]+right[1]
        assert 1 <= cost <= cap
        if info == price*cost:
            return price, iteration+1
        assert info > price*cost
        price = info/cost
    raise AssertionError('Finite policy iteration failed')


def counterexample():
    rows = []
    previous = F()
    for N in (1, 2, 4, 8, 16, 32, 64):
        r, w, _, _ = coefficients(N)
        k, iterations = ratio(r, w, N)
        information = sum((comb(N, j)*r[N, j] for j in range(N+1)), F())
        assert previous <= k <= F(3,4)
        previous = k
        rows.append(dict(cap=N, ordinary_ratio=float(k), exact_ratio=str(k),
                         full_depth_information=float(information), policy_iterations=iterations))
    assert rows[0]['exact_ratio'] == '9/128'
    return dict(law='mu(dd)=2 dd on (0,1/2]', rho='1/4',
                priors={'low':'0','high':'1/4','variance':'1/2-d','work':'1/4'},
                variance_prior_mass='1/4', target_gap='1/4',
                latent_divergence='infinity', genie_ratio_every_finite_cap='infinity',
                ordinary_infinite_cap_lower='9/128', ordinary_infinite_cap_upper='3/4',
                proof='For every stopped prefix of length n>=1, r_s <= (3/8)*n*u_s. Thus I <= (3/8) E_U T <= (3/4) E_qw T, since the work-reference latent density dominates U/2.',
                finite_checks=rows)


def regularization():
    rows = []
    for exponent in (4, 16, 64, 256):
        eps = F(1, 2**exponent)
        # Exact latent integral for q_v^eps=(1-eps)(1/2-d)+eps/8.
        argument = (4-3*eps)*(8-eps)/(eps*(4+3*eps))
        loglo, loghi = log_enclosure(argument)
        cvlo, cvhi = loglo/(8*(1-eps)), loghi/(8*(1-eps))
        cap_rows = []
        previous_info = F()
        for N in (1, 8, 32):
            r, w, _, _ = coefficients(N, eps)
            info = sum((comb(N, j)*r[N, j] for j in range(N+1)), F())
            assert previous_info <= info <= cvlo
            previous_info = info
            k, _ = ratio(r, w, N)
            assert k <= F(3,4)/(1-eps)
            cap_rows.append(dict(cap=N, ordinary_ratio=float(k),
                                 full_depth_information=float(info),
                                 residual_lower=float(cvlo-info),
                                 genie_ratio_lower_from_always_reveal=float(cvlo/N)))
        rows.append(dict(epsilon=f'2^-{exponent}', latent_divergence_interval=[float(cvlo),float(cvhi)],
                         ordinary_infinite_cap_upper=float(F(3,4)/(1-eps)), caps=cap_rows))
    return dict(rows=rows,
                conclusion='For fixed N, C_v^eps/N and e_N^eps diverge as eps->0, although K_infinity^eps converges to finite K_infinity. The N and eps limits cannot be interchanged.')


def polynomial_multiply(a, b):
    c = [F()]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def count_polynomial(n, k, sign):
    p = [F(1)]
    for _ in range(k):
        p = polynomial_multiply(p, [F(1,2), F(sign)])
    for _ in range(n-k):
        p = polynomial_multiply(p, [F(1,2), F(-sign)])
    return [comb(n,k)*x for x in p]


def projection_check(moment, L):
    odd = [2*j+1 for j in range(L)]
    b = [moment(r) for r in odd]
    gram = [[moment(r+s) for s in odd] for r in odd]
    coefficients = solve(gram, b)
    squared_norm = 1-sum((x*y for x,y in zip(b,coefficients)),F())
    assert squared_norm > 0
    norm_upper = 1+sum((abs(c)*F(1,2)**r for r,c in zip(odd,coefficients)),F())
    hmoment = lambda r: moment(r)-sum((c*moment(r+s) for s,c in zip(odd,coefficients)),F())
    assert hmoment(0) == squared_norm
    assert all(hmoment(r) == 0 for r in odd)
    # Verify equality of full count laws at the largest nonidentifying cap.
    N = 2*L
    for k in range(N+1):
        plus, minus = count_polynomial(N,k,1), count_polynomial(N,k,-1)
        assert sum(((a-b)*hmoment(r) for r,(a,b) in enumerate(zip(plus,minus))),F()) == 0
    rho = F(1,8)
    epsilon = rho/(4*norm_upper)
    gap = 2*epsilon*squared_norm
    assert gap > 0
    return dict(cap=N, L=L, projection_coefficients=list(map(str,coefficients)),
                residual_norm_squared=str(squared_norm), residual_sup_bound=str(norm_upper),
                certified_positive_target_gap=str(gap), bias_floor_lower=float(gap/2))


def infinite_identification():
    # An actual infinite-support law accumulating at zero, with exact moments:
    # P(D=2^-j)=2^-j, j>=1; E D^r = 1/(2^(r+1)-1).
    moment = lambda r: F(1,2**(r+1)-1)
    rows = [projection_check(moment,L) for L in range(1,9)]
    # Sharper explicit L=1 witness: h(d)=1-(7/3)d, ||h||_infinity=1.
    assert 1-F(7,3)*moment(1) == F(2,9)
    return dict(law='P(D=2^-j)=2^-j, j>=1', exact_moment='E[D^r]=1/(2^(r+1)-1)',
                explicit_cap_1_and_2_witness='h(d)=1-(7/3)d; q_H,L=1/16 +/- h(d)/32',
                explicit_cap_1_and_2_target_gap='1/72',
                explicit_cap_1_and_2_bias_floor_lower='1/144', rows=rows)


def finite_identification():
    rng = random.Random(20261029)
    count = 0
    for m in range(2,9):
        for trial in range(8):
            # Include closely spaced supports to prevent floating rank tests
            # from silently replacing exact identification by conditioning.
            ds = ([F(1,2**j) for j in range(1,m+1)] if trial % 2 == 0 else
                  [F(1,4)+F(j,10**5) for j in range(m)])
            weights = [F(rng.randrange(1,20)) for _ in ds]
            total = sum(weights)
            weights = [w/total for w in weights]
            moment = lambda r: sum((w*d**r for d,w in zip(ds,weights)),F())
            projection_check(moment,m-1)
            # At N=2m-1, d Q(d^2)=1 interpolates every distinct positive atom.
            matrix = [[d**(2*j+1) for j in range(m)] for d in ds]
            c = solve(matrix,[F(1)]*m)
            assert all(sum((a*b for a,b in zip(row,c)),F()) == 1 for row in matrix)
            count += 1
    # Explicit three-atom witness, matching cap 3 and cap 4.
    ds, weights = [F(1,2),F(1,4),F(1,8)],[F(1,3)]*3
    h = [F(1),F(-10),F(16)]
    low = [F(1,16)-x/512 for x in h]
    high = [F(1,16)+x/512 for x in h]
    assert all(F(1,32)<=q<=F(3,32) for q in low+high)
    gap = sum((w*(a-b) for w,a,b in zip(weights,high,low)),F())
    assert gap == F(7,768)
    for N in (3,4):
        for k in range(N+1):
            difference = sum((w*(qh-ql)*((F(1,2)+d)**k*(F(1,2)-d)**(N-k)
                                              -(F(1,2)-d)**k*(F(1,2)+d)**(N-k))
                              for d,w,qh,ql in zip(ds,weights,high,low)),F())
            assert difference == 0
    return dict(exact_threshold_cases=count, support_sizes='2 through 8',
                explicit_three_atom_low=list(map(str,low)), explicit_three_atom_high=list(map(str,high)),
                explicit_three_atom_target_gap=str(gap),
                explicit_three_atom_result='Positive identification floor at caps 3 and 4; zero floor begins at cap 5.')


def main():
    report = {}
    for name, check in [('pointwise_genie_counterexample',counterexample),
                        ('regularization_and_nonuniformity',regularization),
                        ('infinite_support_identification',infinite_identification),
                        ('finite_support_threshold',finite_identification)]:
        report[name] = check()
        print('PASS',name,flush=True)
    report['status'] = 'PASS'
    report['scope'] = 'Exact finite checks and explicit analytic counterexamples. General weak-star compactness and martingale convergence are assessed analytically, not certified by computation.'
    dest = Path(__file__).with_name('infinite_limit_adversarial_audit_results.json')
    dest.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(dest,flush=True)


if __name__ == '__main__':
    main()
