import math, json, pathlib
import numpy as np
from blind import level_stats, p_level, R
def limits(d, Lmax):
    rows=[]
    S=c=0.0
    for l in range(Lmax+1):
        a,D,En = level_stats(0.5+d, l)
        S += D/p_level(l); c += p_level(l)*En
        rows.append((l,a,S,c))
    return rows
out=[]
for d in [0.5,0.45,0.4,0.35,0.3,0.27,0.25,0.22,0.2,0.18,0.16,0.14,0.12,0.1,0.08,0.06,0.05,0.04]:
    rows = limits(d, 26)
    l,a,S,c = rows[-1]
    l2,a2,S2,c2 = rows[-3]
    var = S - a*a
    G = d*math.sqrt(var*c)
    G2 = d*math.sqrt((S2-a2*a2)*c2)
    out.append((d,G))
    print(f"d={d:.3f}  u={a:.6f} var={var:.4f} c={c:.4f}  G=d*sqrt(var*c)={G:.4f} (L-2: {G2:.4f})  sqrt8*G={math.sqrt(8)*G:.4f}", flush=True)
json.dump(out, open(pathlib.Path(__file__).with_name('limit.json'),'w'))
