"""Product Haar on the unframed radius-one outer sheets; not an orbit search."""
import numpy as np

from haar_slab_bound import bounds
from vertex_slab_orbit import SlabOrbit, direct_outer_J, transform_second


COLUMNS = ('inner_j', 'outer_j', 'center', 'variance', 'draws', 'negative', 'draw_min',
           'draw_max', 'log_draw_loss', 'log_p_upper', 'log_loss_upper')


class HaarProbe:
    def __init__(self):
        # Separate from lattice updates. Replaying an invocation in its original
        # beta/start/sample order also replays the auxiliary fields.
        self.rng = np.random.default_rng(2026112301)

    def measure(self, lat, u, beta, verify, mul, inv):
        orbit = SlabOrbit(lat, u, beta, mul, inv)
        center = orbit.constant.sum()
        variance, log_p, log_loss = bounds(center, orbit.B, orbit.dim)
        q = self.rng.normal(size=(128, *orbit.sites.shape, orbit.dim))
        q /= np.linalg.norm(q, axis=-1, keepdims=True)
        r, b = (q[:, :, parity].reshape(len(q), 2, -1) for parity in (0, 1))
        x = np.einsum('ski,ski->k', r.transpose(1, 0, 2) @ orbit.B, b.transpose(1, 0, 2))
        js = center + x
        outer = orbit.sheet_values(orbit.identity()).sum()
        inner_mask = lat.masks['slab'][0]
        def inner_field(pair):
            swapped = np.where(inner_mask[None, ..., None], pair[::-1], pair)
            return (beta/2)*(lat.traces(pair)-lat.traces(swapped)).sum()
        inner = inner_field(u)
        if verify:
            pair = transform_second(lat, u, orbit.site_field(q[0]), mul, inv)
            np.testing.assert_allclose(lat.traces(pair), lat.traces(u), atol=2e-12, rtol=0)
            np.testing.assert_allclose([direct_outer_J(lat, pair, beta), inner_field(pair)],
                                       [js[0], inner], atol=1e-9*max(1., beta), rtol=0)
        # X and -X have the same Haar law. Its signed tanh mean has sign C.
        # Antithetic partners improve the loss estimate but are not extra IID trials.
        y = np.concatenate((center+x, center-x)) * np.sign(center)
        log_draw_loss = np.log(2.) + np.logaddexp.reduce(-np.logaddexp(0., 2*y)) - np.log(len(y))
        return (inner, outer, center, variance, len(q), (js < 0).sum(), js.min(), js.max(),
                log_draw_loss, log_p, log_loss)
