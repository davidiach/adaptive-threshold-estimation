"""Exact failure-ledger and optional-stopping checks, not universal proof."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'toolkit'))
from threshold_toolkit.confidence_ladders import stage_delta

def optional_stopping_audit(horizon=512):
    # X_t iid Ber(1/4). At fixed n, Var(4 H_n-n)=3n.
    # Chebyshev: P((4H_n-n)^2>12n)<=1/4. Count first exits exactly.
    live={0:1}
    records=[]
    for n in range(1,horizon+1):
        nxt={}
        for k,c in live.items():
            for kk,cc in [(k,3*c),(k+1,c)]:
                if (4*kk-n)**2<=12*n:
                    nxt[kk]=nxt.get(kk,0)+cc
        live=nxt
        if n in [16,32,64,128,256,512]:
            ever=1-F(sum(live.values()),4**n)
            fixed=F(sum(comb(n,k)*3**(n-k) for k in range(n+1)
                        if (4*k-n)**2>12*n),4**n)
            assert fixed<=F(1,4)
            records.append({'n':n,'ever_crossed':str(ever),'fixed_time_tail':str(fixed),
                            'ever_display':float(ever),'fixed_display':float(fixed)})
    assert F(records[-1]['ever_crossed'])>F(42,100)
    return {'model':'iid Bernoulli(1/4), fresh d=1/2 coins',
            'boundary':'(4*heads-n)^2 > 12*n',
            'fixed_time_failure_bound':'1/4','horizon':horizon,
            'records':records,'method':'exact integer path counting, no Monte Carlo'}

def main():
    if not __debug__:
        raise RuntimeError('Run without -O.')
    d = F(1, 100)
    for m in range(501):
        assert sum(stage_delta(d,j) for j in range(m+1)) == d*F(m+1,m+2)
    result = {'scope': 'finite_exact_evidence_not_universal_proof',
              'telescoping_identities': 501,
              'optional_stopping': optional_stopping_audit()}
    target = ROOT / '.runtime/confidence-transfer/anytime.json'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'telescoping_identities': 501,
                     'optional_stopping_failure_at_512':
                     result['optional_stopping']['records'][-1]['ever_display']}, indent=2))


if __name__ == '__main__':
    main()
