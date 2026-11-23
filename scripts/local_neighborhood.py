"""Minimum combined area of two exchanges around fixed local Wilson plaquettes."""
import numpy as np

from nested_face_cut import minimum_nested


def _grow(mask, faces, free):
    """Closed one-step neighborhood in the free-link / plaquette incidence graph."""
    out = mask.copy()
    touched = faces[mask[faces].any(axis=1)].ravel()
    out[touched] = free[touched]
    return out


def _endpoint(lat, free, site):
    mask = np.zeros_like(free)
    mask[lat.faces[lat.pairs.index((0, 1)), site]] = True
    return mask & free


def _regions(lat, pins, target_site):
    free = ~pins.ravel()
    faces = lat.faces.reshape(-1, 4)
    spatial = lat.faces[[i for i, pair in enumerate(lat.pairs) if 3 not in pair]].reshape(-1, 4)
    source, target = (_endpoint(lat, free, site) for site in (0, target_site))
    for widen in (False, True):
        left, right = (_grow(_grow(m, spatial, free) if widen else m, faces, free)
                       for m in (source, target))
        yield source, target, left, right


def neighborhood_masks(lat, pinned, *, report=False):
    if lat.sites.size != 8**4:
        raise ValueError('local measurement uses side eight')
    pins = pinned.ravel()
    faces = lat.faces.reshape(-1, 4)
    free_on_face = ~pins[faces]

    def split(mask):
        return mask[faces].any(axis=1) & (free_on_face & ~mask[faces]).any(axis=1)

    middle = []
    for kind, (source, target, left, right) in zip(('narrow', 'wide'), _regions(lat, pins, 4)):
        small, big, cost = minimum_nested(faces, pins, left, right)
        assert np.all(left <= small) and np.all(small <= big) and not (big & right).any()
        assert not (big & pins).any() and not (left & right).any()
        boundaries = [split(m) for m in (source, small, big, target)]
        assert np.max(np.sum(boundaries, axis=0)) == 1
        counts = [int(b.sum()) for b in boundaries]
        assert counts[1]+counts[2] == cost
        complement = ~pins & ~big
        if report:
            # Reversing the anchors selects a minimum from the opposite side.
            # A disagreement exhibits nonuniqueness; equality is interpreted
            # using residual reachability, not just two agreeing costs.
            rev_small, rev_big, rev_cost = minimum_nested(faces, pins, right, left)
            assert rev_cost == cost
            free = ~pins
            print(kind, 'threshold_links_differ_between_extremes',
                  int((small ^ (free & ~rev_big)).sum()),
                  int((big ^ (free & ~rev_small)).sum()))
            # Sorting a pair hides which mask owns a height-one link. Two
            # cofacial height-one links cannot have opposite owners: both
            # unsorted masks would split their common face.
            band = big & ~small
            component = np.zeros_like(band)
            if band.any():
                component[np.flatnonzero(band)[0]] = True
                while True:
                    grown = _grow(component, faces, band)
                    if np.array_equal(component, grown):
                        break
                    component = grown
            print(kind, 'height_one_component', int(component.sum()), 'of', int(band.sum()))
            print(kind, 'protected', int(left.sum()), int(right.sum()), 'optimal_faces', counts,
                  'total', cost, 'source_side_links', int(small.sum()),
                  'target_side_links', int(complement.sum()), 'extra_links',
                  int((small & ~left).sum()), int((complement & ~right).sum()))
        middle.extend((small, big))
    return (source, *middle, target)


if __name__ == '__main__':
    from interior_geometry import _boundary, _tree_pins
    from replica_shell_probe import Lattice
    # The actual optimizations, and a constructive comparison at larger separation.
    for side in (8, 10):
        lat = Lattice(side, 'SU2')
        pinned = _tree_pins(lat, side)
        if side == 8:
            neighborhood_masks(lat, pinned, report=True)
        for name, (s, t, a, b) in zip(('narrow', 'wide'), _regions(lat, pinned, side//2)):
            boundaries = [_boundary(lat, pinned, m) for m in (s, a, ~pinned.ravel() & ~b, t)]
            assert not (a & b).any() and np.max(np.sum(boundaries, axis=0)) == 1
            print('collars', side, name, 'protected', int(a.sum()), int(b.sum()),
                  'faces', [int(row.sum()) for row in boundaries])
