"""Rebuild the paired-difference figure from the two published reduction tables."""
import argparse
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def paired_rows(directory, extent):
    original, replica = [], []
    for line in (directory / "analysis.tsv").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) == 9 and fields[0] == str(extent) and fields[1].isdigit():
            original.append((int(fields[1]), float(fields[6]), float(fields[7])))
    for line in (directory / "paired-checks.tsv").read_text().splitlines():
        fields = line.split("\t")
        if fields[:2] == ["replica_difference", str(extent)]:
            replica.append((int(fields[2]), float(fields[3]), float(fields[4])))
    expected = list(range(extent // 2 + 1))
    if any([row[0] for row in series] != expected for series in (original, replica)):
        raise ValueError(f"incomplete or unordered table at temporal extent {extent}")
    return original, replica


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    fig, axes = plt.subplots(1, 2, figsize=(10, 4.1), dpi=170, layout="constrained", sharey=True)
    for ax, extent in zip(axes, (8, 16)):
        original, replica = paired_rows(args.directory, extent)
        for series, offset, marker, color, label in (
            (original, -0.11, "o", "#195683", "Original centering"),
            (replica, 0.11, "s", "#b35228", "Independent-replica subtraction"),
        ):
            lag, delta, se = zip(*series)
            ax.errorbar([t + offset for t in lag], [1e6 * y for y in delta],
                        yerr=[1e6 * e for e in se], fmt=marker, ms=4.3, capsize=3,
                        color=color, markerfacecolor="white", lw=1.2, label=label)
        ax.axhline(0, color="#51595f", lw=1)
        ax.set_xticks(range(extent // 2 + 1))
        ax.set_xlabel("Time separation (lattice steps)")
        ax.set_title(f"Temporal extent {extent}", loc="left", fontsize=13)
        ax.grid(axis="y", alpha=0.17)
        ax.spines[["top", "right"]].set_visible(False)
    axes[0].set_ylabel("Ordinary − two-level  (units of 10⁻⁶)")
    fig.legend(*axes[0].get_legend_handles_labels(), loc="outside lower center", ncol=2,
               frameon=False)
    fig.savefig(args.directory / "paired-difference.png", bbox_inches="tight", facecolor="white")


if __name__ == "__main__":
    main()
