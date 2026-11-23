"""Finite periodic mixed-action check using an exact Wilson proposal and an adjoint correction."""
import argparse
from itertools import combinations

import numpy as np
from probe_open_collar import conditional
from replica_shell_probe import mul, inv


class Periodic:
    def __init__(self, side):
        shape=(side,)*4
        coords=np.indices(shape).reshape(4,-1)
        self.plus=np.array([np.ravel_multi_index((coords+d[:,None])%side,shape) for d in np.eye(4,dtype=int)])
        self.minus=np.argsort(self.plus,axis=1)
        self.indices=[np.flatnonzero(coords.sum(axis=0)%2==p) for p in (0,1)]
        self.side=side

    def corners(self,u,i,x):
        paths=[]
        for j in range(4):
            if j==i:
                continue
            back=self.minus[j,x]
            paths.append(mul(u[:,j,self.plus[i,x]],inv(mul(u[:,j,x],u[:,i,self.plus[j,x]]))))
            paths.append(mul(inv(mul(u[:,i,back],u[:,j,self.plus[i,back]])),u[:,j,back]))
        return np.array(paths)

    def moments(self,u):
        faces=[]
        for i,j in combinations(range(4),2):
            faces.append(mul(mul(u[:,i],u[:,j,self.plus[i]]),
                             inv(mul(u[:,j],u[:,i,self.plus[j]])))[...,0])
        p=np.array(faces)
        return np.array([p.mean(axis=(0,2)), ((4*p**2-1)/3).mean(axis=(0,2))])

    def sweep(self,u,beta,adj,rng):
        accepted=0
        for i in range(4):
            for x in self.indices:
                paths=self.corners(u,i,x)
                old=u[:,i,x]
                prop=conditional(paths.sum(axis=0),beta,rng)
                # Scalar part of each quaternion product equals the fundamental trace.
                oldp=(old*inv(paths)).sum(axis=-1)
                newp=(prop*inv(paths)).sum(axis=-1)
                delta=(4/3)*(newp**2-oldp**2).sum(axis=0)
                mask=np.log(rng.random(len(x))) <= adj[:,None]*delta
                accepted+=mask[1].sum()
                u[:,i,x]=np.where(mask[:,:,None],prop,old)
        return accepted/(4*self.side**4)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("beta",type=float,choices=(2.0,2.3,2.5))
    parser.add_argument("seed",type=int)
    parser.add_argument("--same",action="store_true")
    parser.add_argument("--burn",type=int,default=96)
    parser.add_argument("--keep",type=int,default=128)
    args=parser.parse_args()
    box=Periodic(4)
    rng=np.random.default_rng([20261123,round(100*args.beta),args.seed])
    u=np.zeros((2,4,4**4,4)); u[...,0]=1
    if args.seed%2:
        hot=rng.normal(size=u[0].shape)
        u[:]=hot/np.linalg.norm(hot,axis=-1,keepdims=True)
    adj=np.array([0,0 if args.same else -.038])
    for _ in range(args.burn):
        box.sweep(u,args.beta,adj,rng)
    rows=[]; acceptance=[]
    for _ in range(args.keep):
        acceptance.append(box.sweep(u,args.beta,adj,rng))
        p,a=box.moments(u)
        rows.append([*p,*(p**2),*a])
    if args.same and not np.array_equal(u[0],u[1]):
        raise ValueError("Wilson controls diverged")
    print(args.beta,args.seed,args.burn,args.keep,int(args.same),*map(lambda x:f"{x:.12g}",
          [*np.mean(rows,axis=0),np.mean(acceptance)]),sep="\t")
