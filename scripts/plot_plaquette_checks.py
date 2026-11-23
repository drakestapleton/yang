"""Rebuild the paired-difference figure from the two published reduction tables."""
import argparse
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def original_rows(table, extent, column=6):
    original = []
    for line in table.read_text().splitlines():
        fields = line.split("\t")
        if len(fields) == 9 and fields[0] == str(extent) and fields[1].isdigit():
            original.append((int(fields[1]), float(fields[column]), float(fields[column+1])))
    if [row[0] for row in original] != list(range(extent // 2 + 1)):
        raise ValueError(f"incomplete or unordered table {table}")
    return original


def paired_rows(directory, extent):
    original = original_rows(directory / "analysis.tsv", extent)
    replica = []
    for line in (directory / "paired-checks.tsv").read_text().splitlines():
        fields = line.split("\t")
        if fields[:2] == ["replica_difference", str(extent)]:
            replica.append((int(fields[2]), float(fields[3]), float(fields[4])))
    expected = list(range(extent // 2 + 1))
    if [row[0] for row in replica] != expected:
        raise ValueError(f"incomplete or unordered table at temporal extent {extent}")
    return original, replica


def all_pair_rows(table, extent):
    rows = []
    for line in table.read_text().splitlines():
        fields = line.split("\t")
        if fields[:3] == ["all_pairs", str(extent), "difference"]:
            rows.append((int(fields[3]), float(fields[4]), float(fields[5])))
    if [row[0] for row in rows] != list(range(extent // 2 + 1)):
        raise ValueError(f"incomplete or unordered replica table {table}")
    return rows


def confirmation_curves(directory):
    fig, axes = plt.subplots(1, 2, figsize=(10, 4.7), dpi=170, layout="constrained", sharey=True)
    datasets = ((8, "primary-offset-check.tsv", -0.16, "^", "#5d7350", "Original T=8"),
                (16, "primary-offset-check.tsv", 0, "o", "#195683", "Original T=16"),
                (16, "confirmation/analysis.tsv", 0.16, "s", "#b35228", "Confirmation T=16"))
    for ax, title, column in zip(axes, ("Ordinary estimator", "Two-level estimator"), (2, 4)):
        for extent, table, shift, marker, color, label in datasets:
            series = original_rows(directory / table, extent, column)
            lag, value, error = zip(*series)
            ax.errorbar([d+shift for d in lag], [v*1e6 for v in value],
                        yerr=[e*1e6 for e in error], fmt=marker, color=color,
                        markerfacecolor="white", capsize=2.5, ms=4.4, lw=1, label=label)
        ax.axhline(0, color="#51595f", lw=1)
        ax.set_yscale("symlog", linthresh=1)
        ax.set_yticks([-1, 0, 1, 10, 100], labels=["−1", "0", "1", "10", "100"])
        ax.set_xticks(range(9))
        ax.set_title(title, loc="left", fontsize=13)
        ax.set_xlabel("Time separation (lattice steps)")
        ax.grid(axis="y", alpha=0.17)
        ax.spines[["top", "right"]].set_visible(False)
    axes[0].set_ylabel("Connected correlation  (units of 10⁻⁶)")
    fig.legend(*axes[0].get_legend_handles_labels(), loc="outside lower center", ncol=3,
               frameon=False)
    fig.savefig(directory / "confirmation" / "correlator.png", bbox_inches="tight", facecolor="white")
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--confirmation", action="store_true",
                        help="compare the two independent T=16 cohorts at both fixed offsets")
    args = parser.parse_args()
    columns = 3 if args.confirmation else 2
    fig, axes = plt.subplots(1, columns, figsize=(4.6*columns + 0.8, 4.1),
                             dpi=170, layout="constrained", sharey=True)
    panels = []
    if args.confirmation:
        offsets = ((0.6, "analysis.tsv", "confirmation/original-offset.tsv"),
                   (0.6022, "primary-offset-check.tsv", "confirmation/analysis.tsv"))
        for anchor, first, second in offsets:
            original = original_rows(args.directory / first, 16)
            confirmation = original_rows(args.directory / second, 16)
            panels.append((16, f"Centering offset {anchor}", original, confirmation))
        pairs = "all-replica-pairs.tsv"
        panels.append((16, "Independent-replica subtraction",
                       all_pair_rows(args.directory / pairs, 16),
                       all_pair_rows(args.directory / "confirmation" / pairs, 16)))
        labels = ("Original chains", "Independent confirmation")
        output = args.directory / "confirmation" / "paired-difference.png"
    else:
        for extent in (8, 16):
            panels.append((extent, f"Temporal extent {extent}", *paired_rows(args.directory, extent)))
        labels = ("Original centering", "Independent-replica subtraction")
        output = args.directory / "paired-difference.png"
    for ax, (extent, title, first, second) in zip(axes, panels):
        for series, offset, marker, color, label in (
            (first, -0.11, "o", "#195683", labels[0]),
            (second, 0.11, "s", "#b35228", labels[1]),
        ):
            lag, delta, se = zip(*series)
            ax.errorbar([t + offset for t in lag], [1e6 * y for y in delta],
                        yerr=[1e6 * e for e in se], fmt=marker, ms=4.3, capsize=3,
                        color=color, markerfacecolor="white", lw=1.2, label=label)
        ax.axhline(0, color="#51595f", lw=1)
        ax.set_xticks(range(extent // 2 + 1))
        ax.set_xlabel("Time separation (lattice steps)")
        ax.set_title(title, loc="left", fontsize=13)
        ax.grid(axis="y", alpha=0.17)
        ax.spines[["top", "right"]].set_visible(False)
    axes[0].set_ylabel("Ordinary − two-level  (units of 10⁻⁶)")
    fig.legend(*axes[0].get_legend_handles_labels(), loc="outside lower center", ncol=2,
               frameon=False)
    fig.savefig(output, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    if args.confirmation:
        confirmation_curves(args.directory)


if __name__ == "__main__":
    main()
