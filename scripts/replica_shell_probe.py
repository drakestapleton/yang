"""Fixed-seed CPU probe of two exchange surfaces in periodic 4D SU(2) or compact U(1)."""
import argparse
from itertools import combinations, product
from math import sqrt

import numpy as np


def mul(a, b):
    scalar = a[..., :1] * b[..., :1] - (a[..., 1:] * b[..., 1:]).sum(axis=-1, keepdims=True)
    vector = a[..., :1] * b[..., 1:] + b[..., :1] * a[..., 1:] + np.cross(a[..., 1:], b[..., 1:])
    return np.concatenate((scalar, vector), axis=-1)


def inv(a):
    return a * np.array([1., -1., -1., -1.])


class Lattice:
    def __init__(self, side, group):
        self.group = group
        shape = (side,) * 4
        self.sites = np.arange(side**4)
        coords = np.array(np.unravel_index(self.sites, shape))
        self.parity = coords.sum(axis=0) % 2
        self.plus = np.array([np.ravel_multi_index((coords + d[:, None]) % side, shape) for d in np.eye(4, dtype=int)])
        self.minus = np.argsort(self.plus, axis=1)
        self.pairs = list(combinations(range(4), 2))
        self.faces = np.array([np.stack((i*side**4+self.sites, j*side**4+self.plus[i],
                                         i*side**4+self.plus[j], j*side**4+self.sites), axis=-1)
                               for i, j in self.pairs])
        # Observed spatial plaquettes at (0,0,0,0) and (0,0,0,2).
        self.separated = np.ravel_multi_index((0, 0, 0, 2), shape)
        time = np.minimum(coords[3], side-coords[3])
        slab = np.broadcast_to(time, (4, len(time)))
        ps = np.zeros((4, len(time)), dtype=bool)
        ps.flat[self.faces[0, 0]] = True
        expanded = ps.copy()
        expanded.flat[self.faces[ps.ravel()[self.faces].any(axis=-1)].ravel()] = True
        target = np.zeros_like(ps)
        target.flat[self.faces[0, self.separated]] = True
        self.masks = {'slab': [slab == 0, slab <= 1], 'local': [ps, expanded],
                      'endpoints': [ps, target]}
        for masks in self.masks.values():
            boundaries = []
            for mask in masks:
                inside = mask.ravel()[self.faces]
                boundaries.append(inside.any(axis=-1) & ~inside.all(axis=-1))
                at_source = mask.ravel()[self.faces[0, 0]]
                at_target = mask.ravel()[self.faces[0, self.separated]]
                assert (at_source.all() and not at_target.any()) or (at_target.all() and not at_source.any())
            assert not (boundaries[0] & boundaries[1]).any()

        # Breadth-first tree rooted at the observed plaquette. Store parent layers
        # to propagate parallel transports in batches, including wrapped edges.
        self.layers = []
        seen = {0}
        level = [0]
        while level:
            layer = []
            for parent in level:
                for direction in range(4):
                    for reverse, neighbor in [(False, self.plus), (True, self.minus)]:
                        child = int(neighbor[direction, parent])
                        if child in seen:
                            continue
                        seen.add(child)
                        layer.append((parent, child, direction, reverse))
            if layer:
                self.layers.append(np.array(layer, dtype=int).T)
            level = [edge[1] for edge in layer]

        # Pin three sides of each observed square. The two components have
        # separate roots, and no frame outside either square is adjusted.
        roots = np.array([0, self.separated])
        x1 = self.plus[0, roots]
        self.forest = [np.array([(x, self.plus[i, x], i, 0) for x in roots for i in (0, 1)]).T,
                       np.array([(x, self.plus[1, x], 1, 0) for x in x1]).T]

    def tree_frame(self, u, layers, verify):
        frame = np.zeros((len(u), len(self.sites), 4))
        frame[..., 0] = 1
        for parent, child, direction, reverse in layers:
            source = np.where(reverse, child, parent)
            edge = u[:, direction, source]
            oriented = np.where(reverse[None, :, None], inv(edge), edge)
            frame[:, child] = mul(frame[:, parent], oriented)
        fixed = np.stack([mul(mul(frame, u[:, i]), inv(frame[:, self.plus[i]])) for i in range(4)], axis=1)
        if verify:
            for parent, child, direction, reverse in layers:
                source = np.where(reverse, child, parent)
                assert np.max(np.abs(fixed[:, direction, source]-[1., 0., 0., 0.])) < 1e-10
        return fixed

    def traces(self, u):
        return np.stack([mul(mul(u[:, i], u[:, j, self.plus[i]]),
                             inv(mul(u[:, j], u[:, i, self.plus[j]])))[..., 0] for i, j in self.pairs], axis=1)

    def staple(self, u, i):
        total = np.zeros_like(u[:, i])
        for j in range(4):
            if i == j:
                continue
            # Both paths go from x+i back to x.
            total += mul(u[:, j, self.plus[i]], inv(mul(u[:, j], u[:, i, self.plus[j]])))
            back = self.minus[j]
            total += mul(inv(mul(u[:, i, back], u[:, j, self.plus[i, back]])), u[:, j, back])
        return total

    def sweep(self, u, beta, rng):
        for i in range(4):
            for parity in (0, 1):
                idx = self.sites[self.parity == parity]
                staple = self.staple(u, i)[:, idx]
                old = u[:, i, idx]
                # Symmetric isotropic proposal on SU(2), with a beta-dependent step.
                delta = rng.normal(size=old.shape)
                if self.group == 'U1':
                    delta[..., 2:] = 0
                delta[..., 0] += 1.5 + beta
                delta /= np.linalg.norm(delta, axis=-1, keepdims=True)
                new = mul(old, delta)
                new /= np.linalg.norm(new, axis=-1, keepdims=True)
                change = beta*mul(new-old, staple)[..., 0]
                accept = np.log(rng.random(change.shape)) <= change
                u[:, i, idx] = np.where(accept[..., None], new, old)

    def observe(self, u, beta, verify, colors=False):
        raw = self.traces(u)
        delta = (raw[0, 0, 0]-raw[1, 0, 0])*(raw[0, 0, self.separated]-raw[1, 0, self.separated])
        result = [raw.mean(), delta/2]
        slab_colors = []
        rotations = np.array([[1,1,1,1], [1,1,-1,-1], [1,-1,1,-1], [1,-1,-1,1]])
        if self.group == 'U1':
            rotations = np.ones_like(rotations)
        for fields_u, names in [(u, ('slab', 'local', 'endpoints')),
                                (self.tree_frame(u, self.layers, verify), ('slab', 'local', 'endpoints')),
                                (self.tree_frame(u, self.forest, verify), ('endpoints',))]:
            traces = self.traces(fields_u)
            if verify:
                assert np.max(np.abs(raw-traces)) < 1e-10
            score = traces.sum()
            for name in names:
                masks = self.masks[name]
                fields = []
                for mask in masks:
                    swapped = np.where(mask[None, ..., None], fields_u[::-1], fields_u)
                    fields.append(beta*(score-self.traces(swapped).sum())/2)
                if names == ('endpoints',):
                    caps = []
                    color_fields = []
                    staples = self.staple(fields_u, 0)
                    for site, measured in zip((0, self.separated), fields):
                        free = self.plus[1, site]
                        link_diff = fields_u[0, 0, free]-fields_u[1, 0, free]
                        staple_diff = staples[0, free]-staples[1, free]
                        cap = abs(beta)*np.linalg.norm(link_diff)*np.linalg.norm(staple_diff)/2
                        caps.append(cap)
                        if colors:
                            rotated_links = fields_u[1, 0, free]*rotations
                            rotated_staples = staples[1, free]*rotations
                            color_fields.append(beta*mul(fields_u[0, 0, free]-rotated_links,
                                                         staples[0, free]-rotated_staples)[:, 0]/2)
                        if verify:
                            assert abs(measured-beta*mul(link_diff, staple_diff)[0]/2) < 1e-9
                            assert abs(measured) <= cap + 1e-9
                if colors and name == 'slab' and fields_u is not u:
                    # The outer slab has its boundary off the source slice.
                    # Rotate only the second framed replica, then exchange.
                    for rot in rotations:
                        colored = fields_u.copy()
                        colored[1] *= rot
                        swapped = np.where(masks[1][None, ..., None], colored[::-1], colored)
                        slab_colors.append(np.tanh(beta*(score-self.traces(swapped).sum())/2))
                        if verify:
                            rotated = u.copy()
                            rotated[1] *= rot
                            assert np.max(np.abs(self.tree_frame(rotated, self.layers, verify)-colored)) < 1e-9
                attenuation = np.prod(np.tanh(fields))
                factors = np.abs(np.tanh(fields))
                # Stable loss avoids subtracting a rounded tanh from one.
                tails = np.exp(-2*np.abs(fields))
                losses = 2*tails/(1+tails)
                result.extend([abs(attenuation), delta*attenuation/2, abs(delta*attenuation)/2,
                               losses[0], factors[0]*losses[1], float(factors[0] <= 0.9),
                               factors[0]*float(factors[1] <= 0.9)])
                if names == ('endpoints',):
                    threshold = np.arctanh(0.9)
                    result.extend([float(caps[0] <= threshold), factors[0]*float(caps[1] <= threshold)])
                    if colors:
                        color_products = np.tanh(color_fields).prod(axis=0)
                        mean_abs = np.abs(color_products).mean()
                        abs_mean = abs(color_products.mean())
                        result.extend([mean_abs, abs_mean, mean_abs-abs_mean, abs(delta)*abs_mean/2])
                        if verify:
                            assert abs(color_products[0]-attenuation) < 1e-9
                            for rot in rotations:
                                rotated = u.copy()
                                rotated[1] *= rot
                                aligned = self.tree_frame(rotated, self.forest, verify)
                                assert np.max(np.abs(aligned[1]-fields_u[1]*rot)) < 1e-10
                                assert np.max(np.abs(self.traces(rotated)-raw)) < 1e-10
                if verify:
                    orbit = []
                    for bits in product((0, 1), repeat=2):
                        other = fields_u.copy()
                        for bit, mask in zip(bits, masks):
                            if bit:
                                other = np.where(mask[None, ..., None], other[::-1], other)
                        values = self.traces(other)
                        obs = (values[0, 0, 0]-values[1, 0, 0])*(values[0, 0, self.separated]-values[1, 0, self.separated])
                        weight = beta*(values.sum()-score)
                        expected = -2*np.dot(bits, fields)
                        assert abs(weight-expected) < 1e-9 and abs(obs-delta*(-1)**sum(bits)) < 1e-12
                        orbit.append((weight, obs))
                    logw, obs = np.transpose(orbit)
                    w = np.exp(logw-logw.max())
                    assert abs(np.dot(w, obs)/w.sum()-delta*attenuation) < 1e-10
        if colors:
            mean_abs = np.abs(slab_colors).mean()
            abs_mean = abs(np.mean(slab_colors))
            result.extend([mean_abs, abs_mean, mean_abs-abs_mean])
        return result


def run():
    arg = argparse.ArgumentParser(description=__doc__)
    mode = arg.add_mutually_exclusive_group()
    mode.add_argument('--colors', action='store_true', help='Average signed endpoint factors over four relative color orientations.')
    mode.add_argument('--outer-spectrum', action='store_true', help='Emit one row per sample with the full rigid color-orbit extrema before tanh.')
    mode.add_argument('--vertex-shell', action='store_true', help='Test shared vertex gauges on the unframed outer slab (side 4).')
    mode.add_argument('--haar-shell', action='store_true', help='Measure product Haar weight on the outer vertex sheets (side 4).')
    mode.add_argument('--middle-cut', action='store_true', help='Compare a minimum-face middle cut and a slab at separation three (side 6).')
    arg.add_argument('--group', choices=('SU2', 'U1'), default='SU2')
    arg.add_argument('--side', type=int, default=4)
    arg.add_argument('--warmup', type=int, default=128)
    arg.add_argument('--samples', type=int, default=128)
    arg.add_argument('--stride', type=int, default=2)
    arg.add_argument('--beta', type=float, nargs='+', default=[0, 0.1, 0.5, 2.3])
    opt = arg.parse_args()
    if not np.isfinite(opt.beta).all() or opt.side < 4 or opt.side % 2 or opt.samples < 16 or opt.samples % 8 or opt.stride < 1 or opt.warmup < 0 or min(opt.beta) < 0:
        arg.error('Use an even side >= 4, samples divisible by 8 and >= 16, positive stride and nonnegative beta and warmup.')
    if (opt.vertex_shell or opt.haar_shell) and opt.side != 4:
        arg.error('The dense shared-vertex diagnostic is limited to side 4.')
    if opt.middle_cut and opt.side != 6:
        arg.error('The three-exchange comparison uses side 6 and time separation 3.')
    lat = Lattice(opt.side, opt.group)
    masks = ['slab', 'local', 'endpoints', 'tree_slab', 'tree_local', 'tree_endpoints', 'forest_endpoints']
    keys = ['trace', 'raw_cov'] + [mask+'_'+stat for mask in masks for stat in
            ('abs_factor', 'signed_cov', 'abs_bound', 'first_loss', 'second_weighted_loss',
             'first_moderate', 'second_weighted_moderate')]
    keys += ['forest_endpoints_first_moderate_cs', 'forest_endpoints_second_weighted_moderate_cs']
    if opt.colors:
        keys += ['color_mean_abs', 'color_abs_mean', 'color_cancellation', 'color_abs_bound', 'color_outer_slab_mean_abs',
                 'color_outer_slab_abs_mean', 'color_outer_slab_cancellation']
    measure = None
    if opt.outer_spectrum:
        from outer_slab_spectrum import COLUMNS, measure
    elif opt.vertex_shell:
        from vertex_shell_probe import COLUMNS, VertexProbe
        measure = VertexProbe(lat).measure
    elif opt.haar_shell:
        from haar_shell_probe import COLUMNS, HaarProbe
        measure = HaarProbe().measure
    elif opt.middle_cut:
        from middle_cut_probe import COLUMNS, MiddleCut
        measure = MiddleCut(lat).measure
    if measure is not None:
        columns = ('sample', *COLUMNS)
    else:
        columns = tuple(part for k in keys for part in (k, k+'_batch_se'))
    print('group\tside\twarmup\tsamples\tstride\tbeta\tstart\tseed\t'+'\t'.join(columns), flush=True)
    for ib, beta in enumerate(opt.beta):
        for start in ('hot', 'cold'):
            seed = 41123+2*ib+(start == 'cold')
            rng = np.random.default_rng(seed)
            u = rng.normal(size=(2, 4, len(lat.sites), 4))
            if opt.group == 'U1':
                u[..., 2:] = 0
            u /= np.linalg.norm(u, axis=-1, keepdims=True)
            if start == 'cold':
                u[:] = 0
                u[..., 0] = 1
            # Check the local Metropolis increment against the complete Wilson action.
            trial = u.copy()
            proposal = np.array([0.5, 0.5, 0.5, 0.5])
            if opt.group == 'U1':
                proposal = np.array([0., 1., 0., 0.])
            trial[0, 2, -1] = proposal
            diff = mul(proposal-u[0, 2, -1], lat.staple(u, 2)[0, -1])[0]
            assert abs(diff-(lat.traces(trial)-lat.traces(u)).sum()) < 1e-10
            for _ in range(opt.warmup):
                lat.sweep(u, beta, rng)
            samples = []
            prefix = f'{opt.group}\t{opt.side}\t{opt.warmup}\t{opt.samples}\t{opt.stride}\t{beta:g}\t{start}\t{seed}\t'
            for j in range(opt.samples):
                for _ in range(opt.stride):
                    lat.sweep(u, beta, rng)
                if measure is not None:
                    row = measure(lat, u, beta, j % 32 == 0, mul, inv)
                    print(prefix+str(j)+'\t'+'\t'.join(f'{v:.12g}' for v in row))
                    continue
                samples.append(lat.observe(u, beta, verify=(j % 32 == 0), colors=opt.colors))
            if measure is not None:
                continue
            batch = np.array(samples).reshape(8, -1, len(keys)).mean(axis=1)
            values = np.stack((batch.mean(axis=0), batch.std(axis=0, ddof=1)/sqrt(8)), axis=1).ravel()
            print(prefix+'\t'.join(f'{v:.8g}' for v in values), flush=True)


if __name__ == '__main__':
    run()
