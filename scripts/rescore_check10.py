"""Rescore archived five-operator Schwinger–Dyson fits under the temporal estimates."""
from math import hypot, pi, sqrt, tanh
from pathlib import Path

source = Path(__file__).resolve().parents[1] / "evidence/check10_gb10_run.tsv"
lip = hypot(8 / (9 * pi), 3 * pi / 32)
print("side", "beta", "step", "F_isotropic", "F_TV", "F_W1", "F_W2_trial",
      "TG_adj", "rectangle", "square", "crown", "isotropic", "TV_trial", "W1_trial",
      "W2_trial", sep="\t")
seen = set()
for line in source.read_text().splitlines():
    fields = line.split("\t")
    if not fields[0].isdigit():
        continue
    side, beta, step = int(fields[0]), float(fields[1]), int(fields[2])
    key = side, beta, step
    if key in seen:
        raise ValueError(f"duplicate row: {key}")
    seen.add(key)
    f, a, r, s, c = map(lambda x: abs(float(x)), fields[4:9])
    fs = [9*f, 7*f, 14*lip*f, 7*f/sqrt(3)]
    perturb = [14*tanh(2*a), 45*r, 42*s, 60*c]
    isotropic = fs[0] + 18*tanh(2*a) + sum(perturb[1:])
    # Each published coupling is rounded to six decimals. The maximum possible
    # error in the reconstructed score is (9+36+45+42+60)*0.5e-6.
    if abs(isotropic-float(fields[9])) > 0.000097:
        raise ValueError(f"isotropic score outside rounding bound: {key}")
    values = [*fs, *perturb, isotropic, *(x + sum(perturb) for x in fs[1:])]
    print(side, f"{beta:.2f}", step, *(f"{v:.6f}" for v in values), sep="\t")
if len(seen) != 23:
    raise ValueError(f"expected 23 archived fits, found {len(seen)}")
