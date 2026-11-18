"""Per-gap constants for a proof along the paper's route:
bias <= beta*omega, E V^2 <= sigma*A, E cost <= kappa*A, so MSE <= (beta^2 + sigma*kappa) omega(N^-1/2)^2."""
import math, json, pathlib
import numpy as np
from blind import level_stats, p_level, R
out = []
for L in (4, 6, 8, 10, 12, 14):
    N = 2 ** L; h = 1 / math.sqrt(N)
    beta = sigma = kappa = 0.0; args = {}
    for x in np.geomspace(0.005, 0.5 * math.sqrt(N), 120):
        d = min(0.5, x * h)
        a = min(math.sqrt(N), 1 / d); om = min(1.0, h / d)
        for p in (0.5 + d, 0.5 - d):
            st = [level_stats(p, l) for l in range(L + 1)]
            S = sum(D / p_level(l) for l, (aa, D, En) in enumerate(st))
            c = sum(p_level(l) * En for l, (aa, D, En) in enumerate(st)) + R ** (L + 1)
            ZL = st[L][0]
            err = (1 - ZL) if p > 0.5 else ZL   # P(wrong label) at level L
            if err / om > beta: beta = err / om; args['beta'] = round(float(x), 3)
            if S / a > sigma: sigma = S / a; args['sigma'] = round(float(x), 3)
            if c / a > kappa: kappa = c / a; args['kappa'] = round(float(x), 3)
    K = math.sqrt(beta ** 2 + sigma * kappa)
    print(f"L={L}: beta={beta:.3f} sigma={sigma:.3f} kappa={kappa:.3f} -> K_N=sqrt(beta^2+sigma*kappa)={K:.3f}, sqrt(8)*K_N={math.sqrt(8)*K:.3f}  argmax x={args}", flush=True)
    out.append(dict(L=L, beta=beta, sigma=sigma, kappa=kappa, K_N=K, K_B=math.sqrt(8) * K, args=args))
json.dump(out, open(pathlib.Path(__file__).with_name('route.json'), 'w'), indent=1)
