"""Constants of the Lean proof's method for retuned classifier thresholds.

For the threshold sqrt((a + b*log(cap/n))/n) this evaluates kappa_H and
sigma_H of hoeffding.py: the call cost and call second moment constants that
the Hoeffding bounds of the Lean proof give with exact sums. The proof of
Theorem AB.1 combines them as

    MSE <= 4*(2*beta^2 + sigma*kappa) * omega(B^{-1/2})^2,

with beta = 1 for the bias (Lean) and beta = 1/2 for the sharp bias at small
gaps. The route reaches 11 when 2*beta^2 + sigma*kappa <= 121/4.

The coarse grid uses fewer points than the fine evaluations of the selected
thresholds. b <= 1/4 is left out: see hoeffding.py. Floating point; not a proof.
"""
import json, math, pathlib
from multiprocessing import Pool
from hoeffding import kappa_H, sigma_H

AS = [0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 5.0]
BS = [0.5, 0.75, 1.0, 1.5, 2.0]
FINE = [(1.0, 1.0), (1.5, 1.0), (2.0, 0.5), (2.0, 0.75), (2.5, 0.5), (3.0, 0.5)]


def route(k, s, beta):
    return math.sqrt(4 * (2 * beta ** 2 + k * s))


def coarse(ab):
    a, b = ab
    k = kappa_H(a, b, 100)
    s, u = sigma_H(a, b, 30, 26)
    return dict(a=a, b=b, kappa=k, sigma=s, sigma_at_d2=u, product=k * s,
                route_beta1=route(k, s, 1.0), route_beta_half=route(k, s, 0.5))


def fine(ab):
    a, b = ab
    k = kappa_H(a, b, 400)
    s, u = sigma_H(a, b, 100, 40)
    return dict(a=a, b=b, kappa=k, sigma=s, sigma_at_d2=u, product=k * s,
                route_beta1=route(k, s, 1.0), route_beta_half=route(k, s, 0.5))


def show(r, tag):
    print(f"{tag} a={r['a']:<5} b={r['b']:<5} kappa_H={r['kappa']:.4f} sigma_H={r['sigma']:.4f} "
          f"(at d^2={r['sigma_at_d2']:.2e}) product={r['product']:.3f} "
          f"route beta=1: {r['route_beta1']:.3f}  beta=1/2: {r['route_beta_half']:.3f}", flush=True)


if __name__ == "__main__":
    with Pool(4) as pool:
        grid = pool.map(coarse, [(a, b) for a in AS for b in BS])
        for r in grid:
            show(r, "grid")
        fine_rows = pool.map(fine, FINE)
        for r in fine_rows:
            show(r, "fine")
    json.dump(dict(grid=grid, fine=fine_rows,
                   lean=dict(kappa=26 / 5, sigma=13 / 2, product=169 / 5,
                             route=math.sqrt(4 * (2 + 169 / 5)))),
              open(pathlib.Path(__file__).with_name("params12.json"), "w"), indent=1)
