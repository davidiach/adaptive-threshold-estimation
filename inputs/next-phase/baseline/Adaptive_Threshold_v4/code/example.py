"""A small synthetic observation-oracle example, not an accuracy benchmark."""
import numpy as np
from calibration import estimate_budget, estimate_confidence


def main():
    rng = np.random.default_rng(20261026)
    def new_coin():
        # These latent parameters live inside the oracle, not in the estimator.
        d = float(rng.choice([0.25, 0.10, 0.025]))
        p = 0.5 + d if rng.random() < 0.6 else 0.5 - d
        def observations(n: int) -> int:
            return int(rng.binomial(n, p))
        return observations

    print('RMS-oriented expected-budget estimate:', estimate_budget(new_coin, 4096, rng))
    print('Confidence-amplified estimate:', estimate_confidence(new_coin, 4096, 0.1, rng))
    print('Work can exceed the budget on a run; these outputs are not confidence intervals.')


if __name__ == '__main__':
    main()
