"""Certify Q/K > 1.4604 for one rational eight-atom law (integration review).

The claim needs only a feasible selection: its rigorous objective upper bound
bounds K from above, and the quantile objective's rigorous lower bound bounds
Q from below. It uses neither the bandwise-suffix theorem nor the 8/5 theorem.
The arithmetic is the package module's exact rational interval code.
Apache-2.0.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / 'toolkit'))
sys.path.insert(0, str(HERE.parent))
from runtime_output import compare, output_directory
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw, Precision, band_index, evaluate_selection, exhaustive_certificate,
    quantile_certificate, verify_certificate,
)

EVIDENCE = HERE / 'evidence'
P = Precision(bits=64, log_terms=24)
LAW = json.loads((HERE / 'obstruction_law.json').read_text())
ATOMS = [tuple(pair) for pair in LAW['atoms_gap_mass']]
RHO = F(LAW['rho'])
H = F(LAW['h'])
WITNESS = LAW['feasible_selection']
BOUND = F(LAW['claimed_Q_over_K_strict_lower_bound'])


def main() -> int:
    out, writing = output_directory(__doc__, EVIDENCE)
    law = FiniteGapLaw(ATOMS)
    budget = 1 / H**2
    feasible = evaluate_selection(law, WITNESS, rho=RHO, budget=budget, precision=P)
    quantile = quantile_certificate(law, rho=RHO, budget=budget, precision=P)
    exhaustive = exhaustive_certificate(law, rho=RHO, budget=budget, precision=P)
    for certificate in (quantile, exhaustive):
        assert verify_certificate(certificate, law, rho=RHO, budget=budget)
    q_lower = F(quantile['details']['Q_interval']['lower'])
    assert q_lower > BOUND * feasible.upper, 'Q/K bound failed'
    assert BOUND > F(142132, 100000)
    assert exhaustive['details']['best_hard_witness'] == [str(F(s)) for s in WITNESS]
    record = {
        'scope': 'exact finite lower bound on the best Q <= cK constant; integration review, '
                 'not part of the delivered package',
        'instance': {'law': law.canonical(), 'rho': str(RHO), 'h': str(H),
                     'budget': str(budget)},
        'bands': [band_index(atom.gap) for atom in law.atoms],
        'feasible_selection': WITNESS,
        'feasible_objective_upper': str(feasible.upper),
        'Q_lower': str(q_lower),
        'certified_Q_over_K_strict_lower_bound': LAW['claimed_Q_over_K_strict_lower_bound'],
        'rational_checks': ['Q_lower > (14604/10000)*feasible_objective_upper',
                            '14604/10000 > 142132/100000'],
        'depends_on_band_suffix_lemma': False,
        'Q_over_K_decimal_display': float(q_lower / feasible.upper),
        'supporting_certificates': {'quantile': quantile, 'exhaustive': exhaustive},
    }
    (out / 'obstruction_1_4604.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f"Q/K > {float(BOUND)} certified (display {record['Q_over_K_decimal_display']:.12f})")
    return 0 if writing else compare(out, ['obstruction_1_4604.json'], EVIDENCE)


if __name__ == '__main__':
    sys.exit(main())
