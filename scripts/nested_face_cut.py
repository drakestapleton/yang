"""Exact minimum total split-face count for two nested, face-disjoint masks."""
from itertools import product

import numpy as np

if __package__:
    from .face_min_cut import _Network
else:
    from face_min_cut import _Network


def minimum_nested(faces, pinned, left, right):
    """Return (small, big, total); raise ValueError for invalid or infeasible input.

    All masks are flat boolean arrays indexed by link. The caller supplies the
    two already-protected sets of free links: left <= small <= big <= ~right.
    Neither returned mask contains pins. A face row costs one per mask splitting
    its free links; the two sets of split rows must be disjoint.
    """
    faces = np.asarray(faces)
    pinned, left, right = map(np.asarray, (pinned, left, right))
    if (pinned.ndim != 1 or any(a.dtype != np.bool_ or a.shape != pinned.shape
                                for a in (pinned, left, right))):
        raise ValueError('pinned, left and right must be matching flat boolean arrays')
    if faces.ndim != 2 or faces.shape[1] != 4 or faces.dtype.kind not in 'iu':
        raise ValueError('faces must be an integer array of shape (nfaces, 4)')
    n, m = len(pinned), len(faces)
    if faces.size and (faces.min() < 0 or faces.max() >= n):
        raise ValueError('out-of-range face incidence')
    if (pinned & (left | right)).any():
        raise ValueError('protected sets must contain only free links')
    if (left & right).any():
        raise ValueError('intersecting protected regions')
    if (left[faces].any(axis=1) & right[faces].any(axis=1)).any():
        raise ValueError('one face meets both protected regions')

    # Nodes v and n+v encode high (small) and low (big) membership. Putting
    # all unforced free links at height 1 now witnesses feasibility.
    s = 2*n + 4*m
    t, hard = s + 1, 2*m + 1
    network = _Network(t + 1)
    for v in np.flatnonzero(~pinned).tolist():
        network.add(v, n + v, hard)  # also needed for nonincident free links
    for v in np.flatnonzero(left).tolist():
        network.add(s, v, hard)
    for v in np.flatnonzero(right).tolist():
        network.add(n + v, t, hard)

    free = ~pinned[faces]
    for j, face in enumerate(faces):
        links = dict.fromkeys(face[free[j]].tolist())
        if len(links) < 2:
            continue
        hi = 2*n + 4*j
        lo = hi + 2
        network.add(hi, hi + 1, 1)
        network.add(lo, lo + 1, 1)
        # One shared hard arc: any high link forces every low copy on the face.
        network.add(hi, lo + 1, hard)
        for v in links:
            network.add(v, hi, hard)
            network.add(hi + 1, v, hard)
            network.add(n + v, lo, hard)
            network.add(lo + 1, n + v, hard)

    side = network.source_side(s, t)
    small, big = side[:n].copy(), side[n:2*n].copy()

    def splits(mask):
        labels = mask[faces]
        return (free & labels).any(axis=1) & (free & ~labels).any(axis=1)

    a, b = splits(small), splits(big)
    if ((left & ~small).any() or (big & right).any() or (small & ~big).any()
            or (big & pinned).any() or (a & b).any()):
        raise RuntimeError('cut violates an anchor, pin, nesting, or boundary disjointness')
    total = int(a.sum()) + int(b.sum())
    network.certify(s, t, side, total)
    return small, big, total


def _oracle(faces, pinned, left, right):
    """Independent tiny reference: enumerate pairs, not graph/height gadgets."""
    masks = []
    for bits in product((False, True), repeat=int((~pinned).sum())):
        mask = np.zeros(len(pinned), dtype=bool)
        mask[~pinned] = bits
        if (left & ~mask).any() or (right & mask).any():
            continue
        boundary = set()
        for j, face in enumerate(faces):
            labels = {bool(mask[v]) for v in face if not pinned[v]}
            if len(labels) == 2:
                boundary.add(j)
        masks.append((mask, boundary))
    best = None
    for small, a in masks:
        for big, b in masks:
            if not (small & ~big).any() and not a.intersection(b):
                cost = len(a) + len(b)
                best = cost if best is None else min(best, cost)
    return best


def _controls():
    from itertools import combinations, combinations_with_replacement

    checked = rejected = 0

    def compare(faces, pinned, left, right):
        nonlocal checked, rejected
        original = tuple(x.copy() for x in (faces, pinned, left, right))
        best = _oracle(faces, pinned, left, right)
        try:
            small, big, total = minimum_nested(faces, pinned, left, right)
        except ValueError:
            assert best is None, ('false infeasibility', original, best)
            rejected += 1
        else:
            assert best == total and type(total) is int, (original, best, total)
            assert small.dtype == big.dtype == np.bool_
            assert small.shape == big.shape == pinned.shape
            assert not (small & ~big).any()
            assert not (big & pinned).any()
            assert not (left & ~small).any() and not (big & right).any()
            boundaries = []
            for mask in (small, big):
                boundaries.append({j for j, face in enumerate(faces)
                                   if len({bool(mask[v]) for v in face
                                           if not pinned[v]}) == 2})
            assert boundaries[0].isdisjoint(boundaries[1])
            assert sum(map(len, boundaries)) == total
        assert all(np.array_equal(a, b) for a, b in zip(
            original, (faces, pinned, left, right)))
        checked += 1

    # Exhaust every multiset of up to two face supports on three links, all
    # pin sets, and all disjoint free left/right sets. Pad singleton/triple
    # supports by repeated incidences; repeated rows remain distinct costs.
    supports = [c for k in range(1, 4) for c in combinations(range(3), k)]
    families = [()] + [(f,) for f in supports]
    families += list(combinations_with_replacement(supports, 2))
    for family in families:
        faces = np.array([list(f) + [f[-1]]*(4-len(f)) for f in family],
                         dtype=int).reshape(-1, 4)
        for statuses in product(range(4), repeat=3):
            status = np.array(statuses)
            compare(faces, status == 3, status == 1, status == 2)

    # Both cuts are necessary. Expanding these already-protected anchors would
    # wrongly make the chain infeasible. Link 3 tests an isolated left anchor.
    faces = np.array([[0, 1, 1, 1], [1, 2, 2, 2]])
    pinned = np.zeros(4, dtype=bool)
    left = np.array([True, False, False, True])
    right = np.array([False, False, True, False])
    compare(faces, pinned, left, right)
    small, big, total = minimum_nested(faces, pinned, left, right)
    assert total == 2 and small[3] and big[3]
    assert np.array_equal(small, left)
    assert np.array_equal(big, np.array([True, True, False, True]))

    # Two-versus-two split of a four-link hyperedge costs one, not four;
    # duplicating its row charges it twice. The second face forces the other cut.
    faces = np.array([[0, 1, 2, 3], [0, 1, 2, 3], [2, 3, 4, 4]])
    left = np.array([True, True, False, False, False])
    right = np.array([False, False, False, False, True])
    compare(faces, np.zeros(5, bool), left, right)
    assert minimum_nested(faces, np.zeros(5, bool), left, right)[2] == 3
    # All pins, empty graph, and isolated right/unforced.
    compare(np.empty((0, 4), int), np.zeros(0, bool),
            np.zeros(0, bool), np.zeros(0, bool))
    compare(np.array([[0, 1, 2, 3]]), np.ones(4, bool),
            np.zeros(4, bool), np.zeros(4, bool))
    compare(np.empty((0, 4), int), np.zeros(3, bool),
            np.array([True, False, False]), np.array([False, True, False]))

    # Dropping disjointness makes this impossible instance seem feasible:
    # choose both masks equal to left, splitting the same face twice. Merely
    # enforcing per-link nesting does not forbid that double split.
    direct = np.array([[0, 1, 1, 1]])
    left, right = np.array([True, False]), np.array([False, True])
    compare(direct, np.zeros(2, bool), left, right)
    assert len({bool(left[v]) for v in direct[0]}) == 2
    assert not (left & ~left).any()

    # Crossed masks may have disjoint boundaries but are not nested. This
    # control is not a claim to prove the separate uncrossing theorem.
    crossed_a = np.array([True, True, False, False])
    crossed_b = np.array([True, False, True, False])
    assert (crossed_a & ~crossed_b).any() and (crossed_b & ~crossed_a).any()
    crossed_faces = np.array([[0, 1, 1, 1], [0, 2, 2, 2]])
    a = {j for j, f in enumerate(crossed_faces) if len(set(crossed_a[f])) == 2}
    b = {j for j, f in enumerate(crossed_faces) if len(set(crossed_b[f])) == 2}
    assert a and b and a.isdisjoint(b)
    compare(np.array([[0, 1, 1, 1], [0, 2, 2, 2]]), np.zeros(4, bool),
            np.array([True, False, False, False]),
            np.array([False, False, False, True]))

    empty = np.empty((0, 4), int)
    zeros = np.zeros(3, bool)
    invalid = [
        (np.zeros((1, 3), int), zeros, zeros, zeros),
        (np.zeros((1, 4), float), zeros, zeros, zeros),
        (np.array([[0, 1, 2, 3]]), zeros, zeros, zeros),
        (np.array([[-1, 0, 0, 0]]), zeros, zeros, zeros),
        (empty, zeros, np.zeros(3, int), zeros),
        (empty, np.zeros((1, 3), bool), np.zeros((1, 3), bool), np.zeros((1, 3), bool)),
        (empty, zeros, np.zeros(2, bool), zeros),
        (empty, np.array([True]), np.array([True]), np.array([False])),
        (empty, np.array([False]), np.array([True]), np.array([True])),
    ]
    for args in invalid:
        try:
            minimum_nested(*args)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted malformed or contradictory input')

    # Actual feasible flow, then intentional certificate faults.
    net = _Network(3)
    net.add(0, 1, 1)
    net.add(1, 2, 1)
    side = net.source_side(0, 2)
    net.certify(0, 2, side, 1)
    for bad in (0, 2):
        try:
            net.certify(0, 2, side, bad)
        except RuntimeError:
            pass
        else:
            raise AssertionError('accepted false primal value')
    net.residual[1] = 0.5
    try:
        net.certify(0, 2, side, 1)
    except RuntimeError:
        pass
    else:
        raise AssertionError('accepted fractional flow')
    print(f'independent pair oracle: {checked} cases; {rejected} infeasible')
    print('anchors not expanded; pins, isolated links, repeated rows/incidences: PASS')
    print('semantic negatives: double-split and crossed masks are inadmissible: PASS')
    print(f'invalid-input controls: {len(invalid)}; certificate corruption controls: PASS')


if __name__ == '__main__':
    _controls()
