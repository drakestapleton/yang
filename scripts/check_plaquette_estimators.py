#!/usr/bin/env python3
"""Paired outer-chain contrasts, disjoint-replica centering and periodic fits."""
import argparse
import gzip
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

from analyze_plaquette_spectrum import estimate, means, read_chain


def jack_cov(deletions):
    deviations = deletions - deletions.mean(axis=0)
    return (len(deletions)-1)/len(deletions) * deviations.T @ deviations


def slice_data(path):
    with gzip.open(path, "rt") as f:
        tag, T, chain, burn, n, inner = f.readline().split()
        n, T = int(n), int(T)
        bits = np.loadtxt(f, dtype=np.uint64, usecols=(4,5,6), max_rows=n*T)
        if tag != "SLAB4" or f.read().splitlines() != ["END"]:
            raise ValueError(f"{path}: invalid or incomplete slab-four chain")
        return bits.view(np.float64).reshape(n,T,3)


def replicas(a,b):
    n,T,_ = a.shape
    phase = (np.arange(T)[None,:] - np.arange(n)[:,None]) % T
    direct = a[:,:,0]-b[:,:,0]
    sub = a[:,:,1]-b[:,:,1]
    second = a[:,:,2]+b[:,:,2]-2*a[:,:,1]*b[:,:,1]
    result = [[],[]]
    for d in range(T//2+1):
        result[0].append(0.5*np.mean(direct*np.roll(direct,-d,axis=1)))
        target = np.roll(phase,-d,axis=1)
        inside = (phase%4!=0) & (target%4!=0) & ((phase//4!=target//4) | (d==0))
        selected = inside if np.any(inside) else (phase%4!=0) ^ (target%4!=0)
        product = second if d==0 else sub*np.roll(sub,-d,axis=1)
        result[1].append(0.5*np.mean(product[selected]))
    return np.array(result)


def sign_check(deltas):
    """Flip the entire lag vector of each independent chain together."""
    n = len(deltas)
    observed = np.abs(deltas.mean(axis=0))/(deltas.std(axis=0,ddof=1)/np.sqrt(n))
    signs = 2*((np.arange(2**n)[:,None] >> np.arange(n))%2)-1
    m = signs @ deltas / n
    se = np.sqrt(np.maximum((np.mean(deltas**2,axis=0)-m**2)/(n-1),0))
    scores = np.abs(m)/se
    picked = observed.argmax()
    return picked, observed[picked], np.mean(scores[:,picked]>=observed[picked]-1e-12), np.mean(
        scores.max(axis=1)>=observed[picked]-1e-12)


def periodic_fit(y, chol, lags, T):
    wy = np.linalg.solve(chol,y)
    def residual(E):
        # Parameterize the forward amplitude at the first fitted lag.
        phi = np.exp(-E*(lags-lags[0]))+np.exp(-E*(T-lags-lags[0]))
        wphi = np.linalg.solve(chol,phi)
        amplitude = max(0.0,wphi@wy/(wphi@wphi))
        return np.sum((wy-amplitude*wphi)**2)
    optimum = minimize_scalar(residual,method="bounded",bounds=(0,12),options={"xatol":1e-10})
    if not optimum.success or not 1e-6 < optimum.x < 12-1e-6:
        return np.nan, np.nan
    return optimum.x, optimum.fun


def fits(T, method, y, deletions):
    cov = jack_cov(deletions)
    upper = 0
    for d in range(1,len(y)):
        if y[d] <= 3*np.sqrt(cov[d,d]):
            break
        upper=d
    print(f"# fit_support T={T} method={method} contiguous_positive_lags={upper}")
    # The original T=8 cohort supports at most 1..3 in the two-level series.
    # Repeat that common window at T=16 for an extent comparison.
    for stop in sorted({upper,min(3,upper)}):
        previous=None
        # Each fit has two parameters. Keep at least one degree of freedom.
        for start in range(1,stop-1):
            ds=np.arange(start,stop+1)
            chol=np.linalg.cholesky(cov[np.ix_(ds,ds)])
            energy,chi=periodic_fit(y[ds],chol,ds,T)
            deleted=np.array([periodic_fit(v[ds],chol,ds,T)[0] for v in deletions])
            error=np.sqrt(jack_cov(deleted))
            change=change_se=np.nan
            if previous is not None:
                change=energy-previous[0]
                change_se=np.sqrt(jack_cov(deleted-previous[1]))
            print("fit",T,method,start,stop,*(f"{x:.8g}" for x in (energy,error,chi)),
                  len(ds)-2,*(f"{x:.8g}" for x in (change,change_se)),sep="\t")
            previous=energy,deleted



def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("files",nargs="+",type=Path)
    p.add_argument("--anchor",type=float,default=0.6)
    args=p.parse_args()
    groups={}
    for path in sorted(args.files):
        (T,c,burn,n,inner,width),obs=read_chain(path,args.anchor)
        g=groups.setdefault(T,{})
        if c in g: raise ValueError("duplicate chain")
        g[c]=means(obs),slice_data(path)
    print("# sign_flip: T, strongest positive lag, absolute studentized difference, fixed-lag and max-lag probabilities")
    print("# replica: T, method, d, replica estimate and SE, original minus replica and paired SE")
    print("# replica_difference: T, d, replica ordinary minus two-level and paired SE")
    print("# fit: T, method, inclusive start and stop, E and SE, correlated chi-square, degrees of freedom, change dropping earliest and paired SE")
    for T,g in sorted(groups.items()):
        ids=sorted(g)
        if not (ids==list(range(10,26)) or T==16 and ids==list(range(40,56))):
            raise ValueError("expected one full matched 16-chain cohort")
        cols=np.array([g[c][0] for c in ids])
        count=len(ids)
        nlag=T//2+1
        projected=cols[:,1:].reshape(count,2,nlag)
        delta=projected[:,0]-projected[:,1]
        strongest,score,p_fixed,p_all=sign_check(delta[:,1:])
        print(f"sign_flip\t{T}\t{strongest+1}\t{score:.8g}\t{p_fixed:.8g}\t{p_all:.8g}")
        def connected(keep):
            return np.array(estimate(cols[keep].tolist(),args.anchor)[1:]).reshape(2,nlag)
        all_rows=np.arange(count)
        full=connected(all_rows)
        leave=np.array([connected(all_rows[all_rows!=j]) for j in all_rows])
        pair_values=np.array([replicas(g[i][1],g[j][1]) for i,j in zip(ids[::2],ids[1::2])])
        ref=pair_values.mean(axis=0)
        n_pairs=len(pair_values)
        pair_ids=np.arange(n_pairs)
        ref_leave=np.array([pair_values[pair_ids!=i].mean(axis=0) for i in pair_ids])
        matched_leave=np.array([connected(all_rows[all_rows//2!=i]) for i in pair_ids])
        rd = ref[0]-ref[1]
        rse=np.sqrt(np.diag(jack_cov(ref_leave[:,0]-ref_leave[:,1])))
        for d in range(nlag):
            print("replica_difference",T,d,f"{rd[d]:.9g}",f"{rse[d]:.9g}",sep="\t")
        j,z,p_one,p_max=sign_check((pair_values[:,0]-pair_values[:,1])[:,1:])
        print(f"sign_flip_replica\t{T}\t{j+1}\t{z:.8g}\t{p_one:.8g}\t{p_max:.8g}")
        for k,method in enumerate(("direct","two_level")):
            ref_se=np.sqrt(np.diag(jack_cov(ref_leave[:,k])))
            diff_se=np.sqrt(np.diag(jack_cov(matched_leave[:,k]-ref_leave[:,k])))
            for d in range(nlag):
                print("replica",T,method,d,*(f"{x:.9g}" for x in
                      (ref[k,d],ref_se[d],full[k,d]-ref[k,d],diff_se[d])),sep="\t")
            fits(T,method,full[k],leave[:,k])
            fits(T,method+"_replica",ref[k],ref_leave[:,k])


if __name__=="__main__":
    main()
