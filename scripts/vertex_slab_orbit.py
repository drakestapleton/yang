"""Radius-one outer slab, unframed pair, second-replica vertex gauges only.

The coordinate witness is feasible, not a claimed minimum. The spectral lower
bound is a binary64 diagnostic, not an interval or exact-arithmetic proof.
"""
import numpy as np


class SlabOrbit:
    """Outer field C + r.B.b on each of two spatial checkerboards.

    `sites[s,color,v]` lists the actual top vertices. Coordinates at those
    sites are unit quaternions (SU2) or unit real-i pairs (embedded U1).
    The other vertices have identity gauge. Each crossing face has a top
    link T and a complementary path P with the *same oriented endpoints*.
    For vertex coordinates x,y, <P,x T y*> = <P y,x T>. Subtract the two
    crossed pairings from the uncrossed pairings, all in beta/2 units.
    """

    def __init__(self, lat, u, beta, mul, inv):
        side = round(len(lat.sites)**0.25)
        if side not in (4, 6) or side**4 != len(lat.sites):
            raise ValueError('dense per-sheet orbit diagnostic supports even sides 4 and 6 only')
        if lat.group not in ('SU2', 'U1') or u.dtype != np.float64 or not np.isfinite(beta):
            raise ValueError('expected a binary64 SU2 or embedded U1 replica pair and finite beta')
        self.dim = d = 2 if lat.group == 'U1' else 4
        self.beta = beta
        self.volume = len(lat.sites)
        mask = lat.masks['slab'][1][0]
        bottom = lat.sites[mask != mask[lat.plus[3]]]
        top = lat.plus[3, bottom]
        times = np.unique(top % side)  # time is last in the sampler's unravel_index
        if len(times) != 2:
            raise ValueError('expected two separate top sheets')
        self.sites = np.array([[top[(top % side == t) & (lat.parity[top] == color)]
                                for color in (0, 1)] for t in times])
        _, _, m = self.sites.shape
        # Local vertex number within a color, separately for each sheet.
        number = np.full(self.volume, -1, dtype=int)
        number[self.sites] = np.arange(m)
        sites = self.sites.reshape(2, 2*m)
        bottom = lat.minus[3, sites]
        basis = np.eye(4)[:d]
        self.constant = np.zeros(2)
        blocks = np.zeros((2, m, d, m, d))
        for i in range(3):
            top_link = u[:, i, sites]
            path = mul(mul(inv(u[:, 3, bottom]), u[:, i, bottom]), u[:, 3, lat.plus[i, bottom]])
            self.constant += (beta/2) * (path*top_link).sum(axis=(0, 2, 3))
            # Row a, column b: <e_a T1, P0 e_b> + <e_a P1, T0 e_b>.
            def pairing(p, t):
                return mul(basis, t[..., None, :]) @ mul(p[..., None, :], basis).swapaxes(-1, -2)
            edges = (-beta/2) * (pairing(path[0], top_link[1]) + pairing(top_link[0], path[1]))
            dst = number[lat.plus[i, sites]]
            for s in range(2):
                v = np.arange(m)
                blocks[s, v, :, dst[s, :m], :] += edges[s, :m]
                blocks[s, dst[s, m:], :, v, :] += edges[s, m:].swapaxes(-1, -2)
        self.B = blocks.reshape(2, m*d, m*d)

    def identity(self):
        q = np.zeros((*self.sites.shape, self.dim))
        q[..., 0] = 1.
        return q

    def generic(self):
        """Fixed, site-varying, configuration-independent control/start field."""
        q = np.random.default_rng(1977).normal(size=(*self.sites.shape, self.dim))
        return q / np.linalg.norm(q, axis=-1, keepdims=True)

    def site_field(self, q):
        """Expand sheet coordinates to a full site field (including U1 padding)."""
        g = np.zeros((self.volume, 4))
        g[:, 0] = 1.
        g[self.sites, :self.dim] = q
        return g

    def _field(self, q, color):
        other = q[:, 1-color].reshape(2, -1)
        B = self.B if color == 0 else self.B.swapaxes(-1, -2)
        return np.einsum('sij,sj->si', B, other).reshape(q[:, color].shape)

    def sheet_values(self, q):
        return self.constant + np.einsum('sva,sva->s', q[:, 0], self._field(q, 0))

    def optimize(self):
        """Exact independent single-vertex updates per color; two fixed starts."""
        best = self.identity()
        values = self.sheet_values(best)
        for q in (best.copy(), self.generic()):
            previous = self.sheet_values(q)
            for _ in range(96):
                for color in (0, 1):
                    field = self._field(q, color)
                    norm = np.linalg.norm(field, axis=-1, keepdims=True)
                    np.divide(-field, norm, out=q[:, color], where=norm != 0)
                current = self.sheet_values(q)
                better = current < values
                best[better] = q[better]
                values = np.minimum(values, current)
                if np.all(previous-current <= 1.e-10 * np.maximum(1., np.abs(previous))):
                    break
                previous = current
        return best

    def dual_lower(self, q):
        """H=[[0,B],[B.T,0]]/2; shift each vertex block by lambda_v I.

        For K=H-diag(lambda), ||q||^2=N gives per-sheet lower bound
        C + sum(lambda) + N*eigmin(K). Choose lambda_v=q_v.(Hq)_v
        at the feasible witness; the inequality holds even off stationarity.
        Only one (N*d)^2 shifted matrix is needed at a time, never a 4D
        volume-wide matrix. No claim that these multipliers optimize the dual.
        """
        n = self.sites.shape[1]*self.sites.shape[2]
        k = n*self.dim
        h = k//2
        eps = np.finfo(float).eps
        shifts = np.stack([np.einsum('sva,sva->sv', q[:, c], self._field(q, c))/2
                           for c in (0, 1)], axis=1).reshape(2, n)
        K = np.zeros((k, k))
        lower = 0.
        for s in range(2):
            K[:h, h:] = self.B[s]/2
            K[h:, :h] = K[:h, h:].T
            np.fill_diagonal(K, -np.repeat(shifts[s], self.dim))
            eig = np.linalg.eigvalsh(K)[0]
            # Conservative binary64 *allowance*, not a certified LAPACK error
            # bound. Include beta even if the assembled coefficients cancel;
            # the final N-fold subtraction also cushions the constant and sum.
            margin = 128*eps*k*max(1., abs(self.beta), np.linalg.norm(K, np.inf))
            lower += self.constant[s] + shifts[s].sum() + n*(eig-margin)
        return float(lower)


def transform_second(lat, u, g, mul, inv):
    """Full directed-link gauge transform, independent of the crossing faces."""
    pair = u.copy()
    pair[1] = mul(mul(g, u[1]), inv(g[lat.plus]))
    return pair


def direct_outer_J(lat, pair, beta):
    """Both complete Wilson actions, before and after exchanging outer links."""
    mask = lat.masks['slab'][1]
    swapped = np.where(mask[None, ..., None], pair[::-1], pair)
    return (beta/2)*(lat.traces(pair) - lat.traces(swapped)).sum()


def analyze(lat, u, beta, verify, mul, inv):
    """Return raw identity J, feasible witness J, and floating dual lower J."""
    orbit = SlabOrbit(lat, u, beta, mul, inv)
    identity = orbit.identity()
    q = orbit.optimize()
    raw, witness = (float(orbit.sheet_values(field).sum()) for field in (identity, q))
    lower = orbit.dual_lower(q)
    if not (np.isfinite([lower, witness, raw]).all() and lower <= witness <= raw):
        raise ArithmeticError('nonfinite or unordered vertex-orbit diagnostic')
    # Check both endpoints whenever a negative witness might be reported, even
    # off schedule. The caller must still use a sign tolerance in classification.
    if verify or witness < 0:
        baseline = lat.traces(u)
        fields = (identity, q, orbit.generic()) if verify else (identity, q)
        for field in fields:
            pair = transform_second(lat, u, orbit.site_field(field), mul, inv)
            np.testing.assert_allclose(lat.traces(pair), baseline, atol=2e-12, rtol=0)
            np.testing.assert_allclose(direct_outer_J(lat, pair, beta), orbit.sheet_values(field).sum(),
                                       atol=1e-9*max(1., abs(beta)), rtol=0)
    return raw, witness, lower
