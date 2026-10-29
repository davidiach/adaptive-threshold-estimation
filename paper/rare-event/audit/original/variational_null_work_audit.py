"""Independent audit of Appendix C.5 and Sections 4.1--4.3.

Main analytic checks:
* w_*(d)=min(1,alpha^2/d^2), with integral w_*=rho, maximizes Psi(h)
  for every h. Pointwise Lagrange inequalities are checked exactly.
* The bias subtraction 4b is necessary: a centered one-flip estimator
  on an easy atom plus a tiny hard atom defeats every replacement cb, c<4.
* Optimal ordinary band mass is <=rho (stronger than the printed 3rho).
  A factor-two dyadic selection bound then gives h H_O <=2 Psi(h).
* A true optimal ordinary set can violate the factor-one version.

No manuscript implementation is imported. Arithmetic is rational except
for explicitly labeled displayed approximations. Square roots use exact
integer enclosures when needed.
"""
from fractions import Fraction as F
from math import comb, isqrt, sqrt
from pathlib import Path
import json
import random


def solve(matrix, rhs):
    n = len(rhs)
    a = [list(row)+[v] for row,v in zip(matrix,rhs)]
    for col in range(n):
        pivot = next(i for i in range(col,n) if a[i][col])
        a[col],a[pivot] = a[pivot],a[col]
        value = a[col][col]
        a[col] = [x/value for x in a[col]]
        for i in range(n):
            if i != col:
                value = a[i][col]
                a[i] = [x-value*y for x,y in zip(a[i],a[col])]
    return [row[-1] for row in a]


def sqrt_interval(x, bits=90):
    assert x >= 0
    scale = 1 << bits
    integer = isqrt(x.numerator*scale*scale//x.denominator)
    lo = F(integer,scale)
    hi = lo if lo*lo == x else F(integer+1,scale)
    assert lo*lo <= x <= hi*hi
    return lo,hi


def waterfill(mu,rho):
    remaining = rho
    inverse = sum((w/(d*d) for d,w in mu),F())
    for d,w in sorted(mu):
        a2 = remaining/inverse
        if d*d > a2:
            break
        remaining -= w
        inverse -= w/(d*d)
        assert inverse > 0 and remaining > 0
    a2 = remaining/inverse
    allocation = [min(F(1),a2/(d*d)) for d,w in mu]
    assert sum((w*q for (d,w),q in zip(mu,allocation)),F()) == rho
    return a2,allocation


def psi_with_rational_alpha(mu,rho,alpha,h):
    allocation = [min(F(1),(alpha/d)**2) for d,w in mu]
    assert sum((w*q for (d,w),q in zip(mu,allocation)),F()) == rho
    return sum((w*min(q,h*min(F(1),alpha/d)/d)
                for (d,w),q in zip(mu,allocation)),F())


def psi_interval(mu,rho,h):
    a2,q = waterfill(mu,rho)
    lo = hi = F()
    for (d,w),x in zip(mu,q):
        sl,sh = sqrt_interval(x)
        lo += w*min(x,h*sl/d)
        hi += w*min(x,h*sh/d)
    assert lo <= hi <= rho
    return lo,hi


def make_law(rng,count):
    ds = sorted({F(1,2**rng.randrange(1,9)) for _ in range(count*4)},reverse=True)[:count]
    while len(ds)<count:
        ds.append(ds[-1]/2)
    weights = [F(1,2**rng.randrange(0,12)) for _ in ds]
    total = sum(weights,F())
    weights = [w/total for w in weights]
    mu = list(zip(ds,weights))
    alpha = rng.choice(ds)/rng.choice((1,2,4))
    while True:
        rho = sum((w*min(F(1),(alpha/d)**2) for d,w in mu),F())
        if rho <= F(1,4):
            break
        alpha /= 2
    return mu,rho,alpha


def optimizer_checks():
    rng = random.Random(1928192)
    checks = 0
    saturated = 0
    for _ in range(250):
        mu,rho,alpha = make_law(rng,rng.randrange(1,7))
        a2,q = waterfill(mu,rho)
        assert a2 == alpha*alpha
        saturated += any(x == 1 for x in q)
        for h in (alpha/64,alpha/2,alpha,2*alpha,*[d for d,w in mu]):
            value = psi_with_rational_alpha(mu,rho,alpha,h)
            assert 0 < value <= rho
            price = F(1) if h >= alpha else h/(2*alpha)
            for (d,w),x in zip(mu,q):
                fx = min(x,h*min(F(1),alpha/d)/d)
                for y in (F(),F(1),x,F(rng.randrange(0,101),100)):
                    tangent = fx+price*(y-x)
                    assert tangent >= 0
                    if y <= (h/d)**2:
                        assert y <= tangent
                    else:
                        # Checks (h/d)*sqrt(y)<=tangent without floating sqrt.
                        assert (h/d)**2*y <= tangent*tangent
                    checks += 1
            if h >= alpha:
                assert value == rho
    return dict(atomic_laws=250, laws_with_saturated_atoms=saturated,
                exact_pointwise_optimality_checks=checks,
                optimizer='w_*(d)=min(1,alpha^2/d^2), integral w_*=rho; same optimizer works for every h.')


def conditional_response_checks():
    rng = random.Random(64128)
    count = 0
    for trial in range(100):
        cap = 1+trial%6
        policies = []
        for seed in range(4):
            policy = {}
            def generate(x):
                stop = len(x)==cap or rng.randrange(4)==0
                policy[x] = (stop,F(rng.randrange(-30,31),7))
                if not stop:
                    generate(x+(0,)); generate(x+(1,))
            generate(())
            policies.append(policy)
        def evaluate(policy,p,x=()):
            stop,y = policy[x]
            if stop:
                return y,y*y,F()
            left,right = evaluate(policy,p,x+(0,)),evaluate(policy,p,x+(1,))
            return ((1-p)*left[0]+p*right[0],(1-p)*left[1]+p*right[1],
                    1+(1-p)*left[2]+p*right[2])
        for d in (F(1,2),F(1,4),F(249,1000),F(1,128),F(1,2**20)):
            moments = []
            for sign in (-1,1):
                raw = [evaluate(policy,F(1,2)+sign*d) for policy in policies]
                moments.append([sum((v[j] for v in raw),F())/4 for j in range(3)])
            minus,plus = moments
            response = plus[0]-minus[0]
            assert response*response <= 64*d*d*minus[2]*(minus[1]+plus[1])
            count += 1
    return dict(randomized_ordered_policies=100, exact_gap_checks=count,
                includes='zero-observation decisions, d=1/2, and d=2^-20')


def null_product_checks():
    rng = random.Random(128192)
    count = 0
    minimum_ratio = None
    for trial in range(45):
        mu,rho,alpha = make_law(rng,1+trial%3)
        N = 2*len(mu)-1
        matrix,targets = [],[]
        for d,w in mu:
            for sign in (0,1):
                p = F(1,2)+(2*sign-1)*d
                matrix.append([F(comb(N,k))*p**k*(1-p)**(N-k) for k in range(N+1)])
                targets.append(F(sign))
        outputs = solve(matrix,targets)
        null_second = F()
        for i,(d,w) in enumerate(mu):
            seconds = []
            for sign in (0,1):
                row = matrix[2*i+sign]
                mean = sum((p*y for p,y in zip(row,outputs)),F())
                assert mean == sign
                seconds.append(sum((p*y*y for p,y in zip(row,outputs)),F()))
            assert seconds[1]-seconds[0] == 1
            null_second += w*seconds[0]
        variance = null_second+rho*(1-rho)
        breakpoints = sorted({min(d,alpha) for d,w in mu})
        for bias in (F(),rho/128,rho/64):
            slope = 1-2*bias/rho
            rhs = max((max(F(),psi_with_rational_alpha(mu,rho,alpha,h)-4*bias)/h)**2/192
                      for h in breakpoints)
            # Between breakpoints Psi is affine, so (Psi-4b)/h is monotone.
            # These candidates therefore check the full supremum over h>0.
            assert rhs > 0
            for activation in (F(1),F(1,7),F(1,1024)):
                product = slope*slope*N*(variance+(1-activation)*(rho/2)**2)
                assert product >= rhs
                minimum_ratio = product/rhs if minimum_ratio is None else min(minimum_ratio,product/rhs)
                count += 1
    return dict(exact_unbiased_interpolation_policies=45,
                bias_and_random_activation_cases=count,
                full_h_supremum_checked=True, minimum_actual_product_over_lower_bound=float(minimum_ratio))


def sharp_bias_defect():
    rho,eps,d = F(1,8),F(1,1024),F(1,2**20)
    bias = eps*(1-2*d)/4
    assert bias < rho/64
    pmax = rho+eps*(F(1,2)-d)
    variance = pmax*(1-pmax)
    assert pmax < F(1,2)
    # Y=X-b, with one paid flip. Its bias is +b when q(d)=0 and -b
    # when q(d)=1/2, regardless of the easy-atom allocation.
    for q in (F(),F(1,4),F(1,2)):
        actual_bias = eps*(F(1,2)-d)*(1-2*q)-bias
        assert abs(actual_bias) <= bias
    assert eps-4*bias == 2*eps*d
    false_two_b_lower = (eps-2*bias)**2/(192*d*d)
    assert false_two_b_lower > variance
    # The correct full h-supremum is (eps+sqrt((1-eps)(rho-eps)))^2/48.
    rootlo,roothi = sqrt_interval((1-eps)*(rho-eps))
    correctlo,correcthi = (eps+rootlo)**2/48,(eps+roothi)**2/48
    assert correcthi <= variance
    return dict(law='(1-1/1024) delta_(1/2) + (1/1024) delta_(2^-20)',
                rho=str(rho), estimator='Y=X-b, one flip', bias=str(bias),
                actual_uniform_variance=str(variance), null_work=1,
                wrong_2b_lower_at_h_equals_d=float(false_two_b_lower),
                correct_4b_full_supremum_interval=[float(correctlo),float(correcthi)],
                sharpness='For any fixed c<4, keep eps fixed and let d->0: Psi(d)-c*b >= eps*(1-c/4)+O(d), so the putative product lower bound diverges while V<=1/4.')


def dyadic_two_checks():
    rng = random.Random(293)
    for trial in range(1000):
        n = rng.randrange(1,31)
        s = F(1,2*n+2)
        masses = [s*F(rng.randrange(0,101),100) for _ in range(n)]
        values = [F(2**j) for j in range(n)]
        total = sum((v*f for v,f in zip(masses,values)),F())
        left,selected = s,F()
        for v,f in reversed(list(zip(masses,values))):
            take = min(v,left)
            selected += take*f
            left -= take
        assert total <= 2*selected
    n = 20
    sharp_ratio = F(2**n-1,2**(n-1))
    return dict(exact_dyadic_instances=1000, factor_two_sharpness_ratio=str(sharp_ratio),
                ordinary_mass_improvement='log(1+t)<=sqrt(t) implies sqrt(G(a appended x))<=sqrt(G(a))+sqrt(x); inner optimality therefore forces every ordinary w_j<=rho.',
                ordinary_bound_improvement='h H_O <=2 Psi(h), replacing the printed factor 9.')


def genuine_ordinary_factor_one_counterexample():
    n,rho = 12,F(1,4)
    mu = [(F(1,2**(j+1)),F(1,n)) for j in range(n)]
    h = mu[-1][0]
    ordinary = h*sum((w/d for d,w in mu),F())
    assert ordinary < rho
    # All bands ordinary is an actual inner minimizer: for every subset S,
    # H_S^2 <= rho A_S <= rho Gamma_S, so retaining S cannot reduce cost.
    for mask in range(1<<n):
        H = sum((w/d for j,(d,w) in enumerate(mu) if mask>>j&1),F())
        A = sum((w/(d*d) for j,(d,w) in enumerate(mu) if mask>>j&1),F())
        assert H*H <= rho*A
    psilo,psihi = psi_interval(mu,rho,h)
    assert ordinary > psihi and ordinary <= 2*psilo
    return dict(law='12 dyadic endpoint atoms d_j=2^(-j-1), each mass 1/12',
                rho=str(rho), h=str(h), all_ordinary_is_inner_optimal=True,
                subsets_checked=1<<n, ordinary_contribution=str(ordinary),
                Psi_interval=[float(psilo),float(psihi)],
                ordinary_over_Psi_lower=float(ordinary/psihi),
                conclusion='A universal factor 1 is false even for a genuine optimal ordinary set; factor 2 is valid.')


def boundary_checks():
    rho,h,d = F(1,100),F(1,4),F(1,2)
    ordinary = h/d
    retained = h*F(1,10)/d
    psi = rho
    assert min(rho,ordinary)==min(rho,retained)==rho
    assert ordinary > 9*psi and retained < ordinary
    rows = []
    for exponent in (4,8,16,32):
        gap = F(1,4)+F(1,2**exponent)
        rarity,scale,b = F(1,16),F(1,1024),F(1,2)
        canonical = scale*F(1,4)/b
        exact = scale*F(1,4)/gap
        assert exact < rarity and exact < scale/gap
        assert canonical <= exact <= 2*canonical
        rows.append(dict(gap=str(gap),exact_over_canonical=str(exact/canonical)))
    return dict(outer_cap_counterexample={'rho':str(rho),'h':str(h),'gap':str(d),
                 'ordinary_contribution':str(ordinary),'Psi':str(psi),
                 'conclusion':'The empty retained set minimizes the OUTER-capped objective but violates the ordinary bound. The manuscript correctly selects an INNER minimizer.'},
                fractional_atom_counterexample='For mu=delta_(1/8), rho=1/8, h=1/4, Psi=rho requires a fractional allocation. Restricting w to indicators gives zero.',
                canonical_factor_two_sharpness=rows,
                transfer_branch_squared_ratio='(J/B)/b^2 = 75/4 when b=Psi/64 and J=(15Psi/16)^2/(192h^2), h=B^-1/2')


def main():
    report = {}
    for name,check in [('variational_optimizer',optimizer_checks),
                       ('conditional_response',conditional_response_checks),
                       ('full_null_product',null_product_checks),
                       ('sharp_bias_defect',sharp_bias_defect),
                       ('stronger_ordinary_bound',dyadic_two_checks),
                       ('factor_one_counterexample',genuine_ordinary_factor_one_counterexample),
                       ('boundary_and_transfer_checks',boundary_checks)]:
        report[name] = check()
        print('PASS',name,flush=True)
    assert (F(15,16)**2/192)/(F(1,64)**2)==F(75,4)
    report['status'] = 'PASS'
    report['scope'] = 'Exact finite checks, explicit optimizing allocations, and analytic sharpness/counterexamples. No counterexample to the stated Appendix C.5 or Sections 4.1--4.3 bounds was found.'
    dest = Path(__file__).with_name('variational_null_work_audit_results.json')
    dest.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(dest,flush=True)


if __name__=='__main__':
    main()
