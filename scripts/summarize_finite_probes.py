"""Independent-chain errors for the finite probes, and per-mask reductions on archived pairs."""
import csv
from itertools import groupby
from math import exp, fsum, log10, sqrt
from pathlib import Path
from statistics import fmean, stdev

evidence=Path(__file__).resolve().parents[1]/"evidence"
def rows(filename):
    with (evidence/filename).open() as f:
        return list(csv.DictReader(f,delimiter="\t"))

def emit(*values):
    print(*(f"{x:.9g}" if isinstance(x,float) else x for x in values),sep="\t")

def mean_se(vals):
    return fmean(vals), stdev(vals)/sqrt(len(vals))

def susceptibility(data,key):
    # Connected susceptibility for Np=6*4^4; subtract the independent-chain U statistic.
    p=[float(r["P_"+key]) for r in data]
    disc=fsum(x*y for i,x in enumerate(p) for j,y in enumerate(p) if i!=j)/(len(p)*(len(p)-1))
    return 1536*(fmean(float(r["P2_"+key]) for r in data)-disc)

print("# L,beta,center change and SE,mean absolute center difference and SE")
for (size,beta),group in groupby((r for r in rows("open_collar_pairs.tsv") if r["keep"]=="128"),
                                  lambda r:(int(r["L"]),float(r["beta"]))):
    data=list(group)
    assert sorted(int(r["seed"]) for r in data)==list(range(8))
    emit("collar",size,beta,*mean_se([float(r["flip_minus_plus"]) for r in data]),
         *mean_se([float(r["mean_abs_difference"]) for r in data]))

print("# beta,delta plaquette and SE,Wilson and mixed susceptibilities,paired change and jackknife SE,acceptance")
for beta,group in groupby((r for r in rows("mixed_action_pairs.tsv") if r["same"]=="0"),lambda r:float(r["beta_F"])):
    data=list(group)
    assert sorted(int(r["seed"]) for r in data)==list(range(8))
    delta=lambda sample:susceptibility(sample,"mix")-susceptibility(sample,"W")
    deletions=[delta(data[:j]+data[j+1:]) for j in range(8)]
    emit("mixed",beta,*mean_se([float(r["P_mix"])-float(r["P_W"]) for r in data]),
         susceptibility(data,"W"),susceptibility(data,"mix"),delta(data),7/sqrt(8)*stdev(deletions),
         fmean(float(r["accept_mix"]) for r in data))

print("# start,mask,estimator,median half-action loss J,log10 mean MH acceptance,log10 mean 1-|tanh J|")
aligned=rows("check_aligned_cut.tsv")
for start in ("hot","cold"):
    for mask in ("narrow1","narrow2"):
        data=[r for r in aligned if r["start"]==start and r["mask"]==mask]
        assert [int(r["sample"]) for r in data]==list(range(64))
        for key in ("original_J","aligned_J"):
            vals=sorted(float(r[key]) for r in data)
            # Ordinary MH ratio is exp(-2J), where J=beta/2 * (trace_before-trace_after).
            acceptance=fmean(exp(min(0,-2*j)) for j in vals)
            loss=fmean(2*exp(-2*abs(j))/(1+exp(-2*abs(j))) for j in vals)
            emit("exchange",start,mask,key,(vals[31]+vals[32])/2,log10(acceptance),log10(loss))
