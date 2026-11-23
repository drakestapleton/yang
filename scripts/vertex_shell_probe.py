"""Fixed local gauge averages of the unframed two-slab Wilson estimator."""
import numpy as np

from vertex_slab_orbit import analyze


COLUMNS = ('inner_j', 'outer_j', 'witness_j', 'dual_lower_j', 'checker_j', 'pattern_j',
           'pattern_checker_j', 'inner_abs', 'weighted_mean_abs', 'weighted_abs_mean',
           'weighted_cancellation', 'log_weighted_loss')


class VertexProbe:
    def __init__(self, lat):
        mask = lat.masks['slab'][1][0]
        top = lat.plus[3, mask != mask[lat.plus[3]]]
        # Outside these sheets every gauge is the identity. Fixed auxiliary seed:
        # fields are the same across chain starts and beta, independent of samples.
        identity = np.zeros((len(lat.sites), 4))
        identity[:, 0] = 1
        checker = np.ones((len(lat.sites), 1))
        checker[top, 0] = 1 - 2*lat.parity[top]
        pattern = identity.copy()
        q = np.random.default_rng(20261123).normal(size=(len(top), 4))
        if lat.group == 'U1':
            q[:, 2:] = 0
        pattern[top] = q / np.linalg.norm(q, axis=1, keepdims=True)
        self.fields = (identity*checker, pattern, pattern*checker)

    def measure(self, lat, u, beta, verify, mul, inv):
        outer, witness, lower = analyze(lat, u, beta, verify, mul, inv)
        traces = lat.traces(u)
        score = traces.sum()
        inner_mask, outer_mask = lat.masks['slab']

        def exchange(pair, mask):
            swapped = np.where(mask[None, ..., None], pair[::-1], pair)
            return beta*(score - lat.traces(swapped).sum())/2

        inner = exchange(u, inner_mask)
        if verify:
            np.testing.assert_allclose(outer, exchange(u, outer_mask), atol=1e-9, rtol=0)
        pair = u.copy()
        js = [outer]
        for h in self.fields:
            pair[1] = mul(mul(h, u[1]), inv(h[lat.plus]))
            js.append(exchange(pair, outer_mask))
            if verify:
                np.testing.assert_allclose(lat.traces(pair), traces, atol=1e-10, rtol=0)
                np.testing.assert_allclose(exchange(pair, inner_mask), inner, atol=1e-9, rtol=0)
        if verify:
            # Bipartite center flip negates every crossed dot product, not the
            # original plaquette traces. Both pairs must have the same midpoint.
            np.testing.assert_allclose(js[0]+js[1], js[2]+js[3], atol=1e-9, rtol=0)
        a = abs(np.tanh(inner))
        t = np.tanh(js)
        pos, neg = np.maximum(t, 0).mean(), np.maximum(-t, 0).mean()
        cancel = 2*min(pos, neg)
        # 1-|mean t| = mean(1-|t|) + cancel. Keep the logarithm even
        # where all four factors round to one or the loss itself underflows.
        s = -2*np.abs(js)
        log_tail = np.logaddexp.reduce(np.log(2.)+s-np.logaddexp(0., s))-np.log(len(s))
        log_loss = -np.inf if a == 0 else np.log(a)+np.logaddexp(log_tail, np.log(cancel) if cancel else -np.inf)
        return (inner, outer, witness, lower, *js[1:], a, a*(pos+neg), a*abs(pos-neg), a*cancel, log_loss)
