"""Coupled Wilson heat baths on an open SU(2) box with two fixed boundary conditions."""
import argparse
from itertools import product

import numpy as np
from replica_shell_probe import mul, inv


def conditional(staples, beta, rng):
    """Common random numbers for normalized exp(beta Re(q*staple)) dHaar(q)."""
    norm = np.linalg.norm(staples, axis=-1)
    field = beta*norm
    shape = norm.shape
    done = np.zeros(shape, dtype=bool)
    scalar = np.zeros(shape)
    while not done.all():
        u, accept = rng.random((2, shape[1]))
        # Truncated exponential proposal for the scalar component on [-1,1].
        proposed = np.broadcast_to(2*u-1, shape).copy()
        numerator = np.log1p((1-u)*np.expm1(-2*field))
        np.divide(numerator, field, out=proposed, where=field>0)
        proposed = np.where(field>0, 1+proposed, proposed).clip(-1,1)
        take = ~done & (accept**2 <= 1-proposed**2)
        scalar[take] = proposed[take]
        done |= take
    direction = rng.normal(size=(shape[1],3))
    direction /= np.linalg.norm(direction, axis=-1, keepdims=True)
    q = np.concatenate([scalar[...,None], np.sqrt(1-scalar**2)[...,None]*direction],axis=-1)
    pole = np.zeros_like(staples)
    pole[...,0] = 1
    np.divide(inv(staples), norm[...,None], out=pole, where=field[...,None]>0)
    return mul(q,pole)


class Box:
    def __init__(self, side):
        self.side = side
        shape = (side,)*4
        coords = np.indices(shape).reshape(4,-1)
        directions = np.eye(4,dtype=int)
        self.plus = np.array([np.ravel_multi_index((coords+d[:,None])%side,shape) for d in directions])
        self.minus = np.argsort(self.plus,axis=1)
        self.classes = []
        for axis in range(4):
            # An edge on a boundary hyperplane is fixed. No wrapped link is used.
            other = np.delete(coords,axis,axis=0)
            active = (coords[axis]<side-1) & ((other>0)&(other<side-1)).all(axis=0)
            for parity in range(2):
                self.classes.append((axis,np.flatnonzero(active & (coords.sum(axis=0)%2==parity))))
        mid=side//2
        self.center=np.array([np.ravel_multi_index((mid-1,mid-1,z,t),shape)
                              for z,t in product((mid-1,mid),repeat=2)])
        self.changed=np.ravel_multi_index((mid-1,mid-1,mid-1,0),shape)

    def sweep(self, u, beta, rng):
        for i,x in self.classes:
            total = np.zeros_like(u[:,i,x])
            for j in range(4):
                if i==j:
                    continue
                back=self.minus[j,x]
                total += mul(u[:,j,self.plus[i,x]], inv(mul(u[:,j,x],u[:,i,self.plus[j,x]])))
                total += mul(inv(mul(u[:,i,back],u[:,j,self.plus[i,back]])),u[:,j,back])
            u[:,i,x] = conditional(total,beta,rng)

    def observe(self, u):
        x=self.center
        return mul(mul(u[:,0,x],u[:,1,self.plus[0,x]]),
                   inv(mul(u[:,1,x],u[:,0,self.plus[1,x]])))[...,0].mean(axis=1)

    def initial_collar(self, name):
        # Only tangential links on a boundary hyperplane belong to the collar.
        # The unused periodic wrap entries stay at the identity.
        shape = (self.side,)*4
        coords = np.indices(shape).reshape(4, -1)
        u = np.zeros((4, self.side**4, 4))
        u[..., 0] = 1
        if name == "identity":
            return u
        if name == "sheet":
            mid = self.side // 2
            cut = (coords[0] == mid-1) & (coords[1] >= mid) & (coords[3] == 0)
            u[0, cut, 0] = -1
        elif name == "rough":
            rng = np.random.default_rng([self.side, 230, 314159])
            for axis in range(4):
                tangential = np.delete(coords, axis, axis=0)
                mask = (coords[axis] < self.side-1) & ((tangential == 0) | (tangential == self.side-1)).any(axis=0)
                values = rng.normal(size=(mask.sum(), 4))
                u[axis, mask] = values / np.linalg.norm(values, axis=1, keepdims=True)
        else:
            raise ValueError(f"unknown collar {name}")
        return u

    def pair(self, beta, seed, burn, keep, identical, collar="identity"):
        rng=np.random.default_rng([self.side,round(100*beta),seed,261123])
        u = np.repeat(self.initial_collar(collar)[None], 2, axis=0)
        if seed%2:
            hot=rng.normal(size=(4,self.side**4,4))
            hot/=np.linalg.norm(hot,axis=-1,keepdims=True)
            for i,x in self.classes:
                u[:,i,x]=hot[i,x]
        if not identical:
            u[1,0,self.changed] *= -1
        pinned = u[:,0,self.changed].copy()
        for _ in range(burn):
            self.sweep(u,beta,rng)
        rows=[]
        for _ in range(keep):
            self.sweep(u,beta,rng)
            rows.append(self.observe(u))
        if identical and not np.array_equal(u[0],u[1]):
            raise ValueError("identical collars diverged")
        if not np.array_equal(u[:,0,self.changed], pinned):
            raise ValueError("fixed collar moved")
        sample=np.array(rows)
        diff=sample[:,1]-sample[:,0]
        return [*sample.mean(axis=0), diff.mean(), np.abs(diff).mean()]


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("side",type=int,choices=(4,6))
    p.add_argument("beta",type=float,choices=(0,2,2.3))
    p.add_argument("seed",type=int)
    p.add_argument("--burn",type=int,default=64)
    p.add_argument("--keep",type=int,default=128)
    p.add_argument("--identical",action="store_true")
    a=p.parse_args()
    v=Box(a.side).pair(a.beta,a.seed,a.burn,a.keep,a.identical)
    print(a.side,a.beta,a.seed,a.burn,a.keep,int(a.identical),*(f"{y:.12g}" for y in v),sep="\t")
