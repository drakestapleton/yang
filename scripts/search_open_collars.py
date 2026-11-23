"""Finite search over backgrounds for the influence of one boundary link."""
from concurrent.futures import ProcessPoolExecutor
from statistics import fmean
import argparse
from probe_open_collar import Box


def run(job):
    collar, seed = job
    return collar, seed, Box(4).pair(2.3, seed, 64, 128, False, collar)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--workers", type=int, default=1)
    args = p.parse_args()
    candidates = ("identity", "sheet", "rough")
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        train = list(pool.map(run, ((c, s) for c in candidates for s in range(70, 74))))
        winner = max(candidates, key=lambda c: abs(fmean(v[2] for name, _, v in train if name == c)))
        hold = list(pool.map(run, ((winner, s) for s in range(80, 88))))
    print("stage", "collar", "seed", "P_base", "P_changed", "signed_change", "absolute_change", sep="\t")
    for phase, rows in (("train", train), ("heldout", hold)):
        for name, seed, values in rows:
            print(phase, name, seed, *(f"{x:.12g}" for x in values), sep="\t")


if __name__ == "__main__":
    main()
