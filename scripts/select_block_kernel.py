"""Read complete training batches, choose the blocking weight, then score matched validation."""
import argparse
from pathlib import Path
from statistics import fmean, stdev

def read_scores(root):
    scores={}
    for path in sorted(root.glob("batch.*/quarter-*-seed-*.tsv")):
        fields=path.stem.split("-")
        quarter,seed=int(fields[1]),int(fields[3])
        text=path.read_text().splitlines()
        if text[-1:]!=["CHECK10_GB10_DONE status=PASS"]:
            raise ValueError(f"incomplete run: {path}")
        rows=[r.split() for r in text if r.startswith("32\t")]
        if [int(r[2]) for r in rows]!=list(range(4)) or not all(r[1]=="2.300000" for r in rows):
            raise ValueError(f"missing scales: {path}")
        stats=[r.split() for r in text if r.startswith("projection_min_sq_and_fallbacks")]
        if len(stats)!=1 or int(stats[0][2])!=0 or float(stats[0][1])<=0:
            raise ValueError(f"projection failure: {path}")
        if (seed,quarter) in scores:
            raise ValueError(f"duplicate seed and weight: {path}")
        scores[seed,quarter]=float(rows[-1][9])
    return scores


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("root",type=Path)
    p.add_argument("--winner",action="store_true")
    args=p.parse_args()
    scores=read_scores(args.root)
    train={w:[scores[s,w] for s in (101,102,103)] for w in range(4)}
    winner=min(train,key=lambda w:(fmean(train[w]),w))
    if args.winner:
        print(winner)
        return
    se=lambda vals:stdev(vals)/len(vals)**0.5
    for w,vals in train.items():
        print("train",w,f"{fmean(vals):.6f}",f"{se(vals):.6f}",sep="\t")
    print("winner_quarters",winner,sep="\t")
    test=list(range(201,207))
    base=[scores[s,2] for s in test]
    chosen=[scores[s,winner] for s in test]
    for name,vals in (("baseline",base),("winner",chosen),("paired_winner_minus_baseline",[a-b for a,b in zip(chosen,base)])):
        print("heldout",name,*(f"{v:.6f}" for v in (fmean(vals),se(vals),min(vals),max(vals))),sep="\t")

if __name__=="__main__":
    main()
