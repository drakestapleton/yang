"""Small exact geometry controls for the finite Wilson and mixed-action samplers."""
import math
import unittest

import numpy as np
from probe_mixed_action import Periodic
from probe_open_collar import Box, conditional
from replica_shell_probe import inv, mul


class FiniteProbeTests(unittest.TestCase):
    def test_full_mixed_action_increment(self):
        box=Periodic(4)
        rng=np.random.default_rng(23050)
        u=rng.normal(size=(2,4,256,4))
        u/=np.linalg.norm(u,axis=-1,keepdims=True)
        before=box.moments(u)
        x=np.array([42]); axis=2
        old=u[:,axis,x].copy()
        paths=box.corners(u,axis,x)
        new=np.roll(old,1,axis=-1)
        u[:,axis,x]=new
        direct=6*256*(box.moments(u)-before)
        oldp=mul(old,paths)[...,0]
        newp=mul(new,paths)[...,0]
        local=np.array([(newp-oldp).sum(axis=(0,2)),(4/3)*(newp**2-oldp**2).sum(axis=(0,2))])
        np.testing.assert_allclose(local,direct,atol=1e-12)

    def test_open_edges(self):
        for side in (4,6):
            box=Box(side)
            for direction,sites in box.classes:
                for x in sites:
                    coords=np.array(np.unravel_index(x,(side,)*4))
                    self.assertLess(coords[direction],side-1)
                    others=np.delete(coords,direction)
                    self.assertTrue(np.all((others>0)&(others<side-1)))
            self.assertFalse(any(axis==0 and box.changed in sites for axis,sites in box.classes))

    def test_tilted_haar_reference(self):
        rng=np.random.default_rng(432121)
        n=65536
        staples=np.zeros((2,n,4)); staples[0,:,0]=6; staples[1,:,2]=2
        v=conditional(staples,2.3,rng)
        np.testing.assert_allclose(np.linalg.norm(v,axis=-1),1,atol=5e-14)
        for trace,norm in ((v[0,:,0],6),(-v[1,:,2],2)):
            a=2.3*norm
            def bessel(k):
                return math.fsum((a/2)**(2*j+k)/(math.factorial(j)*math.factorial(j+k)) for j in range(60))
            mean=bessel(2)/bessel(1)
            for values,reference in ((trace,mean),(trace**2,1-3*mean/a)):
                self.assertLess(abs(values.mean()-reference),5*values.std(ddof=1)/math.sqrt(n))


if __name__=="__main__":
    unittest.main()
