#!/usr/bin/env python3
"""Offline cross-check of the elementary functions used by the interval certificates.

Emulates src/ufbi_math.om (uSin64 15th order, uExp64, uLog64) and the historical pre-dyadic certificate (ivSin64 23rd
order) operation by operation in IEEE binary64 and compares against 50-digit mpmath references.
Evidence only (floating point + sampling); it is not a proof of the error budget.
"""
import math, struct, sys
import mpmath as mp

mp.mp.dps = 50
PI = struct.unpack('<d', struct.pack('<Q', 0x400921fb54442d18))[0]
TWOPI = struct.unpack('<d', struct.pack('<Q', 0x401921fb54442d18))[0]
HALFPI = struct.unpack('<d', struct.pack('<Q', 0x3ff921fb54442d18))[0]
LN2 = struct.unpack('<d', struct.pack('<Q', 0x3fe62e42fefa39ef))[0]
INVLN2 = struct.unpack('<d', struct.pack('<Q', 0x3ff71547652b82fe))[0]


def _reduce(theta):
    k = int(theta / TWOPI)  # truncation toward zero, as `long div theta twopi`
    x = theta - float(k) * TWOPI
    n = 0
    while x > PI and n < 8:
        x -= TWOPI; n += 1
    n = 0
    while x < -PI and n < 8:
        x += TWOPI; n += 1
    if x > HALFPI:
        x = PI - x
    if x < -HALFPI:
        x = -PI - x
    return x


def sin_poly(theta, dens):
    x = _reduce(theta)
    x2 = x * x
    s = 1.0
    for d in dens:
        s = 1.0 - (x2 * s) / d
    return x * s


OLD = [210.0, 156.0, 110.0, 72.0, 42.0, 20.0, 6.0]
NEW = [506.0, 420.0, 342.0, 272.0] + OLD
u_sin = lambda t: sin_poly(t, OLD)
u_cos = lambda t: sin_poly(t + HALFPI, OLD)
iv_sin = lambda t: sin_poly(t, NEW)
iv_cos = lambda t: sin_poly(t + HALFPI, NEW)


def u_exp(v):
    kf = v * INVLN2
    ki = int(kf + 0.5) if kf >= 0.0 else int(kf - 0.5)
    r = v - float(ki) * LN2
    p = 1.0
    for d in (12.0, 11.0, 10.0, 9.0, 8.0, 7.0, 6.0, 5.0, 4.0, 3.0, 2.0):
        p = 1.0 + r * (p / d)
    p = 1.0 + r * p
    return p * math.ldexp(1.0, ki)


def u_log(x):
    bits = struct.unpack('<Q', struct.pack('<d', x))[0]
    e = ((bits >> 52) & 2047) - 1023
    m = struct.unpack('<d', struct.pack('<Q', (bits & 0x000fffffffffffff) | 0x3ff0000000000000))[0]
    if m > 1.4142135623730951:
        m = m * 0.5; e += 1
    t = (m - 1.0) / (m + 1.0)
    t2 = t * t
    s = 1.0 / 15.0
    for d in (13.0, 11.0, 9.0, 7.0, 5.0, 3.0):
        s = 1.0 / d + t2 * s
    s = 1.0 + t2 * s
    return float(e) * LN2 + 2.0 * (t * s)


def scan(name, f, ref, lo, hi, n, rel=False, log_grid=False):
    worst, at = mp.mpf(0), None
    for i in range(n + 1):
        x = lo + (hi - lo) * i / n
        if log_grid:
            x = 2.0 ** (math.log2(lo) + (math.log2(hi) - math.log2(lo)) * i / n)
        r = ref(mp.mpf(x))
        err = abs(mp.mpf(f(x)) - r)
        if rel:
            if r != 0:
                err /= abs(r)
            elif err != 0:
                err = mp.inf
        if err > worst:
            worst, at = err, x
    kind = 'rel' if rel else 'abs'
    print(f"{name:34s} [{lo}, {hi}] n={n}  max_{kind}_err={mp.nstr(worst, 4)} at x={at!r}")
    return float(worst)


N = 200000
print("# elementary-function cross-check vs 50-digit mpmath")
a = scan("uSin64  (15th order, OLD)", u_sin, mp.sin, -8.0, 8.0, N)
b = scan("uCos64  (15th order, OLD)", u_cos, mp.cos, -8.0, 8.0, N)
c = scan("ivSin64 (23rd order, NEW)", iv_sin, mp.sin, -8.0, 8.0, N)
d = scan("ivCos64 (23rd order, NEW)", iv_cos, mp.cos, -8.0, 8.0, N)
e = scan("uExp64", u_exp, mp.exp, -100.0, 100.0, N, rel=True)
f = scan("uLog64", u_log, mp.log, 2.0**-60, 2.0**60, N, rel=True, log_grid=True)
g = scan("uLog64 near 1", u_log, mp.log, 0.5, 2.0, N, rel=True)
h = scan("uLog64 near 1 (abs)", u_log, mp.log, 0.5, 2.0, N)
print(f"old cos(0) = {u_cos(0.0)!r}  (must be 1; old margin 1e-12*|x|+1e-15)")
print(f"new cos(0) = {iv_cos(0.0)!r}")
print("# sampled regression thresholds")
ok = True
for label, val, bound in (("ivSin64 abs <= 4e-15", c, 4e-15), ("ivCos64 abs <= 5e-15", d, 5e-15),
                          ("uExp64 rel <= 3e-14", e, 3e-14), ("uLog64 rel <= 1e-13", max(f, g), 1e-13)):
    good = val <= bound
    ok = ok and good
    print(f"{label:26s} observed={val:.3e}  {'OK' if good else 'VIOLATED'}")
print("old uSin64/uCos64 exceed the old margin 1e-12:", a > 1e-12 or b > 1e-12)
sys.exit(0 if ok else 1)
