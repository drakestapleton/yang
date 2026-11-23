#!/usr/bin/env python3
"""Analyze complete Omega chains. Statistical replicas are independently seeded chains."""
import argparse
import gzip
import math
import statistics
import struct
from collections import defaultdict
from pathlib import Path

ANCHOR = 0.6
METHODS = ("direct", "two_level")


def value(bits):
    x, = struct.unpack(">d", int(bits).to_bytes(8, "big"))
    if not math.isfinite(x):
        raise ValueError("nonfinite slice moment")
    return x


def read_chain(path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt") as f:
        tag, T, chain, burn, observations, inner = f.readline().split()
        T, chain, burn, observations, inner = map(int, (T, chain, burn, observations, inner))
        if tag not in ("BEGIN", "SLAB4") or T not in (8, 16) or min(burn, observations, inner) <= 0:
            raise ValueError(f"{path}: invalid run header")
        width = 4 if tag == "SLAB4" else 2
        rows = []
        for k in range(observations):
            direct, sub, sub2 = [], [], []
            for t in range(T):
                fields = f.readline().split()
                if len(fields) != 7 or list(map(int, fields[:4])) != [T, chain, k, t]:
                    raise ValueError(f"{path}: missing or reordered observation {k}, slice {t}")
                p, m, m2 = map(value, fields[4:])
                if max(abs(p), abs(m), abs(m2)) > 1.00001 or m2 + 2e-14 < m*m:
                    raise ValueError(f"{path}: invalid plaquette or second moment")
                if t % width == k % width and abs(p-m) > 2e-14:
                    raise ValueError(f"{path}: frozen slice changed")
                direct.append(p - ANCHOR)
                sub.append(m - ANCHOR)
                sub2.append(m2 - 2 * ANCHOR * m + ANCHOR**2)
            products = []
            for d in range(T//2+1):
                products.append(statistics.fmean(x*direct[(t+d) % T] for t,x in enumerate(direct)))
            for d in range(T//2+1):
                # Interior products factor only across distinct slabs. If no such pair
                # exists for this lag, use one boundary and one interior endpoint.
                phase = k % width
                origins = []
                mixed = []
                for t in range(T):
                    u, v = (t-phase) % T, (t+d-phase) % T
                    if u % width and v % width and (not d or u//width != v//width):
                        origins.append(t)
                    if bool(u % width) != bool(v % width):
                        mixed.append(t)
                origins = origins or mixed
                products.append(statistics.fmean(sub[t]*sub[(t+d) % T] if d else sub2[t]
                                                 for t in origins))
            rows.append([statistics.fmean(direct), *products])
        if f.read().splitlines() != ["END"]:
            raise ValueError(f"{path}: incomplete or concatenated chain")
    return (T, chain, burn, observations, inner, width), rows


def means(rows):
    return [statistics.fmean(col) for col in zip(*rows, strict=True)]


def estimate(chains):
    mean, *p = means(chains)
    # Ordered cross-chain U statistic for the squared one-point expectation.
    n = len(chains)
    disc = math.fsum(a[0]*b[0] for i,a in enumerate(chains)
                     for j,b in enumerate(chains) if i != j) / (n*(n-1))
    return [mean + ANCHOR, *(v-disc for v in p)]


def jk_error(values):
    n = len(values)
    return (n-1) / math.sqrt(n) * statistics.stdev(values)


def jackknife(chains):
    full = estimate(chains)
    leave = [estimate(chains[:i]+chains[i+1:]) for i in range(len(chains))]
    return full, leave


def summary(chains, T):
    full, leave = jackknife(chains)
    nlag = T//2+1
    print(f"# T={T} chains={len(chains)} one_point={full[0]:.9g} SE={jk_error([r[0] for r in leave]):.3g}")
    print("T\td\tdirect\tdirect_SE\ttwo_level\ttwo_level_SE\tdifference\tpaired_SE\tagreement")
    for d in range(nlag):
        a, b = d+1, d+1+nlag
        direct_se = jk_error([r[a] for r in leave])
        sub_se = jk_error([r[b] for r in leave])
        diff = full[a] - full[b]
        diff_se = jk_error([r[a]-r[b] for r in leave])
        agreement = "unresolved"
        if full[a] > 3*direct_se and full[b] > 3*sub_se:
            agreement = "within_3SE" if abs(diff) <= 3*diff_se else "outside_3SE"
        print(T, d, *(f"{x:.9g}" for x in
              (full[a], direct_se, full[b], sub_se, diff, diff_se)), agreement, sep="\t")
    print("T\tmethod\td\tcosh_energy\tSE\tdelta_from_previous\tpaired_SE\tplateau_pair")
    for method, name in enumerate(METHODS):
        last = None
        for d in range(1,nlag):
            i = method*nlag+d+1
            # Reflection on the finite circle makes both neighbors coincide at its midpoint.
            right = i-1 if d == T//2 else i+1
            e = []
            for r in [full,*leave]:
                if min(r[i-1], r[i], r[right]) <= 0:
                    break
                ratio = (r[i-1]+r[right])/(2*r[i])
                if ratio < 1:
                    break
                e.append(math.acosh(ratio))
            # Do not infer energies from a triplet with an unresolved member.
            resolved = all(full[j] > 3*jk_error([r[j] for r in leave]) for j in (i-1,i,right))
            if len(e) != len(leave)+1 or not resolved:
                print(T, name, d, "unresolved", "-", "-", "-", "undetermined", sep="\t")
                last = None
                continue
            delta = ["-", "-", "undetermined"]
            if last is not None:
                change = e[0] - last[0]
                error = jk_error([a-b for a,b in zip(e[1:], last[1:])])
                if abs(change) + 2*error <= 0.20:
                    status = "within_tolerance"
                elif abs(change) - 2*error > 0.20:
                    status = "outside_tolerance"
                else:
                    status = "undetermined"
                delta = [f"{change:.8g}", f"{error:.6g}", status]
            print(T, name, d, f"{e[0]:.8g}", f"{jk_error(e[1:]):.6g}", *delta, sep="\t")
            last = e


def compare(label, left, right):
    """Contrast independent groups, including their separate one-point estimates."""
    l, lj = jackknife(left)
    r, rj = jackknife(right)
    print(f"# comparison={label} independent groups, two_level, difference and SE")
    print("one_point_contrast", label, f"{l[0]-r[0]:.9g}",
          f"{math.hypot(jk_error([v[0] for v in lj]), jk_error([v[0] for v in rj])):.9g}", sep="\t")
    for d, (i,j) in enumerate(label_indices(left, right)):
        diff = l[i]-r[j]
        se = math.hypot(jk_error([v[i] for v in lj]), jk_error([v[j] for v in rj]))
        print("contrast", label, d, f"{diff:.9g}", f"{se:.9g}", sep="\t")


def label_indices(left, right):
    # Each chain vector has a one-point value followed by two lag series.
    nleft, nright = (len(left[0])-1)//2, (len(right[0])-1)//2
    return [(1+nleft+d, 1+nright+d) for d in range(min(nleft,nright))]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("files", type=Path, nargs="+")
    p.add_argument("--production", action="store_true", help="require the full recorded design")
    args = p.parse_args()
    groups = defaultdict(dict)
    specs = {}
    for path in args.files:
        (T,c,b,n,m,w), rows = read_chain(path)
        if c in groups[T] or specs.setdefault(T,(b,n,m,w)) != (b,n,m,w):
            raise ValueError(f"{path}: duplicate chain or inconsistent run design")
        groups[T][c] = rows
    if args.production and (set(groups) != {8,16} or any(
            set(g) != set(range(10,26)) or specs[T] != (256,512,24,4) for T,g in groups.items())):
        raise ValueError("incomplete production design")
    all_chains = {}
    for T, group in sorted(groups.items()):
        ids = sorted(group)
        if len(ids) < 3:
            raise ValueError("delete-one cross-chain centering requires at least three chains")
        print(f"# burn,observations,inner,slab={specs[T]} chain_ids={ids}")
        for c in ids:
            rows = group[c]
            mid = len(rows)//2
            if mid:
                print(f"# chain {c} {'hot' if c%2 else 'cold'} first_half_P={ANCHOR+means(rows[:mid])[0]:.7f}"
                      f" second_half_P={ANCHOR+means(rows[mid:])[0]:.7f}")
        chains = [means(group[c]) for c in ids]
        all_chains[T] = chains
        summary(chains, T)
        mid = len(chains)//2
        if mid >= 3:
            compare(f"T{T}_first-minus-last", chains[:mid], chains[mid:])
        hot = [row for c,row in zip(ids,chains) if c%2]
        cold = [row for c,row in zip(ids,chains) if not c%2]
        if min(len(hot),len(cold)) >= 3:
            compare(f"T{T}_hot-minus-cold",hot,cold)
    if set(all_chains) == {8,16}:
        compare("T8-minus-T16",all_chains[8],all_chains[16])


if __name__ == "__main__":
    main()
