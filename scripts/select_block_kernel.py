"""Score the prespecified blocking-kernel search and its matched validation seeds."""
import argparse
from dataclasses import dataclass
from math import isfinite, sqrt, tanh
from pathlib import Path
from statistics import fmean, stdev


@dataclass(frozen=True)
class Score:
    total: float
    rectangle: float
    crown: float


def read_scores(root):
    scores = {}
    fine_rows = {}
    for path in sorted(root.glob("batch.*/quarter-*-seed-*.tsv")):
        fields = path.stem.split("-")
        quarter, seed = int(fields[1]), int(fields[3])
        text = path.read_text().splitlines()
        if text[-1:] != ["CHECK10_GB10_DONE status=PASS"]:
            raise ValueError(f"incomplete run: {path}")
        rows = [r.split() for r in text if r.startswith("32\t")]
        if [int(r[2]) for r in rows] != list(range(4)) or any(r[1] != "2.300000" for r in rows):
            raise ValueError(f"missing scales: {path}")
        for r in rows:
            f, a, rect, square, crown = (abs(float(x)) for x in r[4:9])
            total = float(r[9])
            reconstructed = 9*f + 18*tanh(2*a) + 45*rect + 42*square + 60*crown
            if not isfinite(total) or not abs(total - reconstructed) <= 0.000097:
                raise ValueError(f"inconsistent score: {path}")
        if fine_rows.setdefault(seed, rows[0][3:10]) != rows[0][3:10]:
            raise ValueError(f"different fine-field fit within matched seed {seed}")
        stats = [r.split() for r in text if r.startswith("projection_min_sq_and_fallbacks")]
        if len(stats) != 1 or int(stats[0][2]) != 0 or not float(stats[0][1]) > 0:
            raise ValueError(f"projection failure: {path}")
        if (seed, quarter) in scores:
            raise ValueError(f"duplicate seed and weight: {path}")
        scores[seed, quarter] = Score(total, 45*rect, 60*crown)
    return scores


def se(values):
    return stdev(values) / sqrt(len(values))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--winner", action="store_true")
    args = parser.parse_args()
    scores = read_scores(args.root)
    train = {w: [scores[s, w].total for s in (101, 102, 103)] for w in range(4)}
    winner = min(train, key=lambda w: (fmean(train[w]), w))
    if args.winner:
        print(winner)
        return

    print("# train: quarter units, mean alpha, independent-seed SE")
    for w, values in train.items():
        print("train", w, f"{fmean(values):.6f}", f"{se(values):.6f}", sep="\t")
    print("winner_quarters", winner, sep="\t")
    test = range(201, 207)
    expected = {(s, w) for s in (101, 102, 103) for w in range(4)}
    expected.update((s, w) for s in test for w in (winner, 2))
    if set(scores) != expected:
        raise ValueError("held-out records differ from the prespecified design")
    print("# heldout: series, mean, SE, minimum, maximum")
    for field in ("total", "rectangle", "crown"):
        base = [getattr(scores[s, 2], field) for s in test]
        chosen = [getattr(scores[s, winner], field) for s in test]
        changes = [a-b for a, b in zip(chosen, base)]
        for name, values in (("baseline", base), ("winner", chosen), ("paired_change", changes)):
            print("heldout", f"{field}_{name}",
                  *(f"{v:.6f}" for v in (fmean(values), se(values), min(values), max(values))),
                  sep="\t")
    print("heldout_winner_below_one", sum(scores[s, winner].total < 1 for s in test), len(test), sep="\t")


if __name__ == "__main__":
    main()
