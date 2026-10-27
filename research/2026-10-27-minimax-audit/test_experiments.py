"""Independent finite-tape and oracle-port checks before the held-out freeze."""
import json,math,unittest
from pathlib import Path
import experiments as e
import numpy as np
import sys
sys.path.insert(0,str(e.ROOT/'benchmark'))
import reference

class Checks(unittest.TestCase):
    def test_observation_port(self):
        # The real observation channel is the original published-model port.
        for seed in range(10):
            for hidden in [-2.,0.,.75,3.]:
                reference.seed_rng(seed)
                expected=[reference.real_x(hidden) for _ in range(20)]
                reference.seed_rng(seed)
                actual=[e.observation(0,hidden,reference.LOSS) for _ in range(20)]
                np.testing.assert_array_equal(actual,expected)

    def test_decision_against_array_reference(self):
        rng=np.random.default_rng(202610271)
        checks=0
        for tape in [np.zeros(64),np.ones(64),-np.ones(64),*rng.normal(size=(200,64))]:
            for cap in [16,64]:
                for n in [1,2,4,8,16,32,64]:
                    if n>cap:continue
                    values=tape[:n]
                    for factor in [1.,2.,3.]:
                        if n==cap: expected=int(values.mean()>0)
                        elif n<16:expected=-1
                        else:
                            b=math.sqrt(float(values.var(ddof=1))*(1+math.log(cap/n))/n)
                            expected=1 if values.mean()>factor*b else 0 if values.mean() < -b else -1
                        self.assertEqual(e.decision(float(values.sum()),float(values@values),n,cap,factor),expected)
                        checks+=1
        self.assertEqual(checks,7308)

    def test_term_envelopes(self):
        reference.seed_rng(202610272)
        for model in range(7):
            for method in range(3):
                for _ in range(50):
                    v,c=e.term(model,reference.LOSS,256,.1,method)
                    self.assertGreater(c,0);self.assertLessEqual(c,256)
                    self.assertTrue(np.isfinite(v))

    def test_finite_randomization_identity(self):
        p=4.**(-.75)/(1+4.**(-.75))
        for coarse in [0,1]:
            for fine in [0,1]:
                self.assertAlmostEqual((1-p)*coarse+p*(coarse+(fine-coarse)/p),fine)

if __name__=='__main__':unittest.main()
