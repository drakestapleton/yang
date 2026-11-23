"""Conditional product-Haar diagnostics for C + sum_s r_s.T B_s b_s.

See evidence/wilson_haar_bound.md for the real-arithmetic inequalities. The
returned natural log ceilings are binary64 evaluations, not certificates.
"""
import math

import numpy as np


def bounds(constant, B, dim):
    """Return Var(J), log upper P(J<0), log upper (1-|E tanh J|).

    B has shape (2, red_coordinates, blue_coordinates). Each consecutive
    dim-vector is uniform on its unit sphere, independently across all blocks.
    constant is the total of the two sheet constants, not a per-sheet array.
    """
    c = np.asarray(constant)
    if c.ndim or c.dtype.kind not in 'ifu' or not math.isfinite(float(c)):
        raise ValueError('constant must be a finite real scalar')
    c = float(c)
    if isinstance(dim, bool) or not isinstance(dim, (int, np.integer)) or dim <= 0:
        raise ValueError('dim must be a positive integer')
    dim = int(dim)
    B = np.asarray(B)
    if (B.ndim != 3 or B.shape[0] != 2 or
            any(n == 0 or n % dim for n in B.shape[1:]) or B.dtype.kind not in 'ifu'):
        raise ValueError('B requires two real matrices with full dim-blocks on both axes')
    B = np.asarray(B, dtype=np.float64)
    if not np.isfinite(B).all():
        raise ValueError('nonfinite B')
    if not B.any():
        # Strict sign event, including the atom at J=0. Avoid tanh saturation.
        a = abs(c)
        if a < 1.0:
            loss = -a - math.log1p(2 * math.sinh(a / 2)**2)
        else:
            z = -2 * a
            if not math.isfinite(z):
                raise OverflowError('constant-field log loss outside binary64 range')
            loss = math.log(2) + z - math.log1p(math.exp(z))
        return 0.0, -math.inf if c >= 0 else 0.0, loss

    sigma = np.linalg.svd(B, compute_uv=False)
    largest = float(sigma.max())
    scale = largest / dim
    if not (math.isfinite(scale) and scale > 0):
        raise OverflowError('nonzero slab singular scale outside binary64 range')
    # q = (sigma / sigma_max)^2; x = t * sigma_max / dim is dimensionless.
    q = np.square(sigma / largest)
    n = float(q.sum())
    sd = scale * math.sqrt(n)
    var = sd * sd
    h = abs(c) / scale
    if not (math.isfinite(var) and var > 0 and math.isfinite(h)):
        raise OverflowError('variance or normalized offset outside binary64 range')

    # Minimize a convex upper envelope, then evaluate the tighter determinant
    # at that tilt. Stay back from the pole even if the minimizer rounds to 1.
    x = min(0.99, h / (n / 2 + math.hypot(n / 2, h)))

    def log_mgf(x):
        if not 0 <= x < 1:
            raise ValueError('tilt outside the Gaussian determinant domain')
        return -h * x - 0.5 * float(np.log1p(-(x*x) * q).sum())

    # Reflecting J is valid for the absolute loss, NOT for the negative event.
    f = log_mgf(x)
    log_p = min(0.0, f) if c > 0 else 0.0
    loss_x = min(x, 2 * scale)
    loss_f = f if loss_x == x else log_mgf(loss_x)
    return var, log_p, min(0.0, math.log(2) + loss_f)


def _controls():
    """Deterministic checks; no chain samples and no optimizer witnesses."""
    # U(1): the difference of two independent Haar angles is uniform, so
    # J = 1.9 + 2 cos(theta). Loss is a 40-digit Wolfram quadrature reference.
    B = np.zeros((2, 2, 2))
    B[0] = 2 * np.eye(2)
    var, lp, ll = bounds(1.9, B, 2)
    p, loss = math.acos(19/20) / math.pi, 0.28646635974401333155
    assert math.isclose(var, 2.0) and math.log(p) <= lp < 0 and math.log(loss) <= ll <= 0
    print(f'U1 circle: var={var:.12g} p={p:.12g} log_p_upper={lp:.12g} '
          f'loss={loss:.12g} log_loss_upper={ll:.12g}')

    # Independent signs on two sheets: J = 3 + sum of four Rademachers.
    B[:] = np.eye(2)
    var, lp, ll = bounds(3, B, 1)
    loss = 1 - sum(math.comb(4,k)*math.tanh(3 + 2*k - 4) for k in range(5))/16
    assert math.isclose(var, 4) and math.log(1/16) <= lp < 0 and math.log(loss) <= ll < 0
    assert bounds(-3, B, 1) == (var, 0.0, ll)
    print(f'two sheets: var={var:.12g} p={1/16:.12g} log_p_upper={lp:.12g} '
          f'loss={loss:.12g} log_loss_upper={ll:.12g}')
    for a in (1e-100, 0.5, 2.0, 1e100):
        v, l, loss_bound = bounds(3*a, B*a, 1)
        assert math.isclose(v, var*a*a) and math.isclose(l, lp)
        assert loss_bound <= 0
    # t=2 cap matters on a small-amplitude field. A large positive offset
    # also checks a nonzero field past the ordinary exp underflow threshold.
    _, _, limited = bounds(0.1, B*0.001, 1)
    assert limited == 0.0
    _, _, far = bounds(1000, B*0.001, 1)
    assert -2000 < far < -1000
    assert bounds(0, B, 1) == (var, 0.0, 0.0)
    B.fill(0)
    assert bounds(0, B, 1) == (0.0, -math.inf, 0.0)
    for c in (0.01, 2., 1000.):
        v, pplus, lossplus = bounds(c, B, 1)
        vminus, pminus, lossminus = bounds(-c, B, 1)
        assert (v, pplus, vminus, pminus) == (0., -math.inf, 0., 0.)
        exact = -c - (math.log(math.cosh(c)) if c < 100 else c - math.log(2))
        assert lossplus == lossminus and math.isclose(lossplus, exact)
    for c, b, d in [(0, B, 0), (0, B, 3), (0, B[:1], 1), (0, np.full_like(B, math.inf), 1),
                    (math.nan, B, 1), ([1, 2], B, 1), (0, B.astype(complex), 1)]:
        try:
            bounds(c, b, d)
        except ValueError:
            continue
        raise AssertionError('accepted invalid input')
    print('scaling, reflection, t<=2, zero, log-range and invalid-domain controls: PASS')


if __name__ == '__main__':
    _controls()
