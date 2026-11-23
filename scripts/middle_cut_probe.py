"""Middle of a three-exchange family on the periodic side-six torus."""
from itertools import product

import numpy as np

from face_min_cut import minimum_middle

COLUMNS = ('source_faces', 'cut_faces', 'slab_faces', 'target_faces',
           'source_j', 'cut_j', 'slab_j', 'target_j')


class MiddleCut:
    def __init__(self, lat):
        shape = (6,) * 4
        coords = np.array(np.unravel_index(lat.sites, shape))
        depth = coords.sum(axis=0)
        # Each nonroot site backs up one step along its first nonzero coordinate.
        self.layers = []
        self.pinned = np.zeros((4, lat.sites.size), dtype=bool)
        for k in range(1, depth.max()+1):
            child = lat.sites[depth == k]
            direction = np.argmax(coords[:, child] != 0, axis=0)
            parent = lat.minus[direction, child]
            assert np.all(depth[parent] == k-1)
            self.layers.append((parent, child, direction, np.zeros_like(child)))
            self.pinned[direction, parent] = True
        assert self.pinned.sum() == lat.sites.size-1
        pins = self.pinned.ravel()
        self.target_site = np.ravel_multi_index((0, 0, 0, 3), shape)
        faces = lat.faces.reshape(-1, 4)
        def endpoint(site):
            mask = np.zeros_like(pins)
            mask[lat.faces[0, site]] = True
            return mask & ~pins
        source, target = endpoint(0), endpoint(self.target_site)
        cut, minimum = minimum_middle(faces, pins, source, target)
        slab = np.tile(np.minimum(coords[3], 6-coords[3]) <= 1, 4) & ~pins
        self.masks = (source, cut, slab, target)
        self.boundaries = []
        active = ~pins[faces]
        for mask in self.masks:
            on = mask[faces]
            self.boundaries.append((active & on).any(axis=1) & (active & ~on).any(axis=1))
        self.counts = tuple(int(b.sum()) for b in self.boundaries)
        assert self.counts[1] == minimum <= self.counts[2]
        assert source.any() and target.any() and not (source & target).any()
        for i in (1, 2):
            assert self.masks[i][source].all() and not self.masks[i][target].any()
            assert np.max(np.sum([self.boundaries[j] for j in (0, i, 3)], axis=0)) <= 1
        # The residual-reachable minimum is already the largest admissible free
        # source side: only the forced target neighborhood is outside it.
        forced_target = target.copy()
        forced_target[faces[self.boundaries[3]].ravel()] = True
        np.testing.assert_array_equal(cut, ~pins & ~forced_target)
        # These free, parallel endpoint links are joined by three successive
        # temporal plaquettes. Each separating mask must split one of the three.
        path = lat.faces[lat.pairs.index((1, 3)), lat.plus[0, :3]]
        assert source[path[0, 0]] and target[path[-1, 2]]
        assert np.array_equal(path[:-1, 2], path[1:, 0])
        assert not pins[path[:, [0, 2]]].any()
        self.split = [faces[b] for b in self.boundaries]

    def measure(self, lat, u, beta, verify, mul, inv):
        v = lat.tree_frame(u, self.layers, verify)
        # Mathematical pins are exactly one; remove transport roundoff on those links.
        v[:, self.pinned] = (1., 0., 0., 0.)
        links = v.reshape(2, -1, 4)
        def score(q):
            return mul(mul(q[:, :, 0], q[:, :, 1]), inv(mul(q[:, :, 3], q[:, :, 2])))[..., 0].sum()
        fields = []
        for mask, face in zip(self.masks, self.split):
            local = links[:, face]
            other = np.where(mask[face][None, ..., None], local[::-1], local)
            fields.append((beta/2)*(score(local)-score(other)))
        if verify:
            raw = lat.traces(u)
            np.testing.assert_allclose(lat.traces(v), raw, atol=2e-12, rtol=0)
            def difference(tr):
                diff = tr[0, 0]-tr[1, 0]
                return diff[0]*diff[self.target_site]
            delta = difference(raw)
            for mid in (1, 2):
                js = np.array([fields[i] for i in (0, mid, 3)])
                orbit = []
                for bits in product((0, 1), repeat=3):
                    exchange = np.zeros(links.shape[1], dtype=bool)
                    for bit, i in zip(bits, (0, mid, 3)):
                        if bit:
                            exchange ^= self.masks[i]
                    pair = np.where(exchange[None, :, None], links[::-1], links).reshape(v.shape)
                    tr = lat.traces(pair)
                    logw = beta*(tr-raw).sum()
                    np.testing.assert_allclose(logw, -2*np.dot(bits, js), atol=2e-8, rtol=0)
                    obs = difference(tr)
                    np.testing.assert_allclose(obs, (-1)**sum(bits)*delta, atol=2e-12, rtol=0)
                    orbit.append((logw, obs))
                weights, obs = np.transpose(orbit)
                weights = np.exp(weights-weights.max())
                np.testing.assert_allclose(weights @ obs / weights.sum(), delta*np.tanh(js).prod(), atol=1e-10, rtol=0)
        return (*self.counts, *fields)
