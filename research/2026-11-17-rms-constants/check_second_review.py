from fractions import Fraction as F
from itertools import product
from math import prod
import sympy as s


t = s.symbols("t", positive=True)
num = s.integrate((1-t**2)**2, (t, 0, 1))
den = 4*s.integrate((1-t**2)*s.sqrt(1+4*t**2), (t, 0, 1))
assert s.simplify(num/den - 128/(15*(17*s.asinh(2) + 14*s.sqrt(5)))) == 0
assert s.integrate(4*t*(1-t)+(1-2*t)**2, (t,0,1)) == 1
assert s.simplify(4*t*(1-t)+(1-2*t)**2) == 1


def word_stats(d, f, m, word):
    # Conditional marginal likelihood and its s-derivative, from the full
    # sign mixture for this coin. This does not use the predictive score formula.
    pos = prod((F(1,2) + y*d for y in word), start=F(1))
    neg = prod((F(1,2) - y*d for y in word), start=F(1))
    return ((1+m)*pos+(1-m)*neg)/2, f*(1-m*m)*(pos-neg)/2


def double_tanh(x):
    return 2*x/(1+x*x)


def enumerate_law(policy, h, gaps, means, max_flips):
    def traverse(history, words):
        i = policy(history)
        if i is None or len(history)==max_flips:
            ps = [word_stats(d, min(1, h/d), m, word) for d, m, word in zip(gaps, means, words)]
            probability = prod(p for p,_ in ps)
            if not probability:
                return F(0), F(0), F(0)
            score = sum(dp/p for p,dp in ps)
            return probability, probability*score**2, probability*len(history)
        children = []
        for y in (-1,1):
            nxt = list(words)
            nxt[i] += (y,)
            children.append(traverse(history+(y,), nxt))
        return tuple(map(sum,zip(*children)))
    return traverse((), [()] * len(gaps))


checks = 0
h = F(1,8)
gaps = (h, 2*h, 4*h)
for tanh_quarter in (F(-1,2), F(-1,5), F(0), F(1,5), F(3,4)):
    mid = double_tanh(tanh_quarter)
    means = (double_tanh(mid), mid, tanh_quarter)
    for first, mode in product(range(3), range(6)):
        def policy(hist):
            if len(hist)>2 and sum(hist) <= -(mode%3+1):
                return None
            return (first + sum(hist) + len(hist)*(mode//2)) % 3
        mass, info, work = enumerate_law(policy, h, gaps, means, 6)
        assert mass == 1 and info <= 4*h*h*work
        checks += 1

weights = (F(1,2), F(1,3), F(1,6))
I = sum(w/d for w,d in zip(weights,gaps))
for signs in product((F(0),F(1,3),F(1,2),F(1)), repeat=3):
    theta = sum(w*q for w,q in zip(weights,signs))
    p = sum(w/(d*I) * (F(1,2)+d*(2*q-1)) for w,d,q in zip(weights,gaps,signs))
    estimate_mean = F(1,2) + I*(2*p-1)/4
    assert estimate_mean == theta
    assert I*I*p*(1-p)/4 <= I*I/16
print(f"Exact weighted integral, four-flip identity, {checks} interleaved Fisher examples and 64 tilted-sampling examples passed.")
