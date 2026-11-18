"""Exact dyadic enclosures for the stopped Fisher price and RMS integral."""
from fractions import Fraction
from functools import cache
from math import isqrt


S = 1 << 40
CENTRAL_END = S*1023//1024


def ceil_div(n, d):
    return -((-n) // d)


def mul_lo(a, b):
    return (a*b) // S


def mul_hi(a, b):
    return ceil_div(a*b, S)


def sqrt_hi(x):
    k = isqrt(S*x)
    return k if k*k == S*x else k+1


@cache
def series_lo(u):
    """Lower bound for integral x^2/(1-u^2 x^2) dx on [0,1]."""
    w = mul_lo(u, u)
    power, total = S, 0
    for j in range(256):
        total += power // (2*j+3)
        power = mul_lo(w, power)
        if power == 0:
            break
    return total


@cache
def price_hi(m):
    """Upper bound on the admissible work multiplier P(m), in units of 1/S."""
    m2lo, m2hi = mul_lo(m,m), mul_hi(m,m)
    v = S-m2lo
    m4lo = mul_lo(m2lo,m2lo)
    m8lo = mul_lo(m4lo,m4lo)
    power, poly = S, 0
    for j in range(12):
        poly += ceil_div(power, 2*j+1)
        power = mul_hi(power, m2hi)
    extra = 2001*S + 160*m8lo
    return ceil_div(1000*v*(S+mul_hi(v,poly)), extra)


def quadratic_nonnegative(q0, q1, q2):
    if min(q0, q0+q1+q2) < 0:
        return False
    if q2 > 0 and -2*q2 < q1 < 0:
        return 4*q2*q0 >= q1*q1
    return True


def covers_box(m0, m1, u0, u1):
    # x=m*u. y is a lower bound on u*(u-m)*H(u,r) for every r.
    xlo, xhi = mul_lo(m0, u0), mul_hi(m1, u1)
    if u0 >= m1:
        y = mul_lo(mul_lo(u0, u0-m1), series_lo(u0))
    else:
        # A negative term occurs only for u<m, so u<=min(u1,m1).
        umax = min(u1, m1)
        hhi = ceil_div(S*S, 2*(S-mul_hi(umax, umax)))
        y = -mul_hi(mul_hi(umax, m1-u0), hhi)
    if S+y <= 0:
        return False
    left, c, p = S-xhi, mul_hi(xhi, xhi), price_hi(m0)
    # Exact lower polynomial in r, cleared of positive scale factors.
    return quadratic_nonnegative(
        left*(S+y)*S - p*S*S,
        -left*((S+y)*c + y*S) + p*xlo*S,
        left*y*c,
    )


def verify_price():
    stack = [(0, CENTRAL_END, 0, S)]
    leaves = 0
    while stack:
        m0, m1, u0, u1 = stack.pop()
        if covers_box(m0, m1, u0, u1):
            leaves += 1
        elif m1-m0 >= u1-u0 and m1-m0 > 1:
            mid = (m0+m1)//2
            stack.extend([(m0, mid, u0, u1), (mid, m1, u0, u1)])
        elif u1-u0 > 1:
            mid = (u0+u1)//2
            stack.extend([(m0, m1, u0, mid), (m0, m1, mid, u1)])
        else:
            raise ValueError(f"Unproved price box {(m0,m1,u0,u1)} at scale {S}")
    return leaves


def integrand_hi(t0, t1):
    # u(t)=(1-t^2)*p(t), p(t)=1-t^4/2.
    t2lo, t2hi = mul_lo(t0,t0), mul_hi(t1,t1)
    t4lo, t4hi = mul_lo(t2lo,t2lo), mul_hi(t2hi,t2hi)
    poly_hi = S - t4lo//2
    # u'(t)=-2t-2t^3+3t^5.
    t3lo, t3hi = mul_lo(t0,t2lo), mul_hi(t1,t2hi)
    t5lo, t5hi = mul_lo(t0,t4lo), mul_hi(t1,t4hi)
    deriv = max(abs(-2*t1-2*t3hi+3*t5lo), abs(-2*t0-2*t3lo+3*t5hi))
    # The direct Fisher bound gives v^2*C <= 1 on the entire interval.
    b = S
    if t1 <= CENTRAL_END:
        vlo, vhi = S-t2hi, S-t2lo
        power, poly = S, 0
        for j in range(12):
            poly += power//(2*j+1)
            power = mul_lo(power,t2lo)
        extra = 2001*S + 160*mul_hi(t4hi,t4hi)
        b = min(S, ceil_div(extra*vhi, 1000*(S+mul_lo(vlo,poly))))
    return sqrt_hi(mul_hi(deriv,deriv) + 4*mul_hi(mul_hi(poly_hi,poly_hi),b))


def verify_integral():
    intervals = 1 << 16
    step = S//intervals
    integral_hi = Fraction(sum(integrand_hi(i*step, (i+1)*step)
                               for i in range(intervals)), intervals*S)
    area = Fraction(2,3) - Fraction(1,35)
    return area / (2*integral_hi)


if __name__ == "__main__":
    boxes = verify_price()
    lower = verify_integral()
    assert lower > Fraction(16207, 100000)
    print(f"Certified {boxes} price boxes; exact lower endpoint {lower}.")
    print(f"RMS coefficient > 16207/100000 (enclosure {float(lower):.9f}).")
