"""Test a reversible residual SU(2) alignment on the archived narrow exchange masks."""
import csv
from pathlib import Path

import numpy as np
from middle_cut_probe import MiddleCut
from replica_shell_probe import Lattice, inv, mul

ROOT = Path(__file__).resolve().parents[1]
BETA = 2.3


def rotate(q, rotation):
    out = q.copy()
    out[...,1:] = q[...,1:] @ rotation
    return out


def exchange(links, mask, frame):
    out = links.copy()
    out[0,mask] = rotate(links[1,mask],frame)
    out[1,mask] = rotate(links[0,mask],frame.T)
    return out


def residual(links, exterior):
    # Orthogonal Procrustes on the traceless components of the two exterior fields.
    # These components are untouched by the exchange, so the reverse computes the same frame.
    a,b=links[:,exterior,1:]
    left, _, right=np.linalg.svd(b.T @ a)
    left[:,-1] *= np.linalg.det(left @ right)
    return left @ right


def score(links, faces):
    p=links[:,faces]
    return mul(mul(p[:,:,0],p[:,:,1]), inv(mul(p[:,:,3],p[:,:,2])))[...,0].sum()


def main():
    lat=Lattice(8,"SU2")
    cut=MiddleCut(lat,geometry="local")
    archive=list(csv.DictReader((ROOT/"evidence/wilson_local_beta23.tsv").open(),delimiter="\t"))
    pins=cut.pinned.ravel()
    print("start","sample","mask","original_J","aligned_J","exterior_links",sep="\t")
    if len(archive)!=128:
        raise ValueError("archived design changed")
    for start,seed in (("hot",41123),("cold",41124)):
        rng=np.random.default_rng(seed)
        u=rng.normal(size=(2,4,len(lat.sites),4))
        u/=np.linalg.norm(u,axis=-1,keepdims=True)
        if start=="cold":
            u[:]=0; u[...,0]=1
        for _ in range(64):
            lat.sweep(u,BETA,rng)
        for observation in range(64):
            for _ in range(2):
                lat.sweep(u,BETA,rng)
            g=lat.tree_frame(u,cut.layers,False)
            g[:,cut.pinned]=(1.,0.,0.,0.)
            links=g.reshape(2,-1,4)
            row=archive[observation + (64 if start=="cold" else 0)]
            if (row["start"],int(row["sample"]),int(row["seed"]))!=(start,observation,seed):
                raise ValueError("archive mismatch")
            for k in (1,2):
                mask=cut.masks[k]
                faces=cut.split[k]
                exterior=np.unique(faces[(~mask & ~pins)[faces]])
                frame=residual(links,exterior)
                orig=exchange(links,mask,np.eye(3))
                alt=exchange(links,mask,frame)
                before=score(links,faces)
                j=(before-score(orig,faces))*BETA/2
                aligned=(before-score(alt,faces))*BETA/2
                if abs(j-float(row[f"narrow{k}_j"]))>2e-8:
                    raise ValueError("ordinary exchange differs from archived pair")
                if observation%8==0:
                    np.testing.assert_allclose(frame.T@frame,np.eye(3),atol=2e-14)
                    np.testing.assert_allclose(exchange(alt,mask,residual(alt,exterior)),links,atol=3e-14)
                    # On completely exchanged faces all links share one conjugation.
                    allfaces=lat.faces.reshape(-1,4)
                    np.testing.assert_allclose((score(links,allfaces)-score(alt,allfaces))*BETA/2,aligned,atol=3e-10)
                print(start,observation,f"narrow{k}",f"{j:.12g}",f"{aligned:.12g}",len(exterior),sep="\t")


if __name__=="__main__":
    main()
