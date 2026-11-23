"""Certified unit split-face cut on the free links of a fixed geometry."""
from collections import deque
from itertools import product

import numpy as np


class _Network:
    """Paired residual arcs; even indices are the original directed arcs."""

    def __init__(self, n):
        self.adj = [[] for _ in range(n)]
        self.head = []
        self.residual = []
        self.capacity = []  # original capacities, never changed by augmentation

    def add(self, u, v, capacity):
        i = len(self.head)
        self.adj[u].append(i)
        self.adj[v].append(i + 1)
        self.head.extend((v, u))
        self.residual.extend((capacity, 0))
        self.capacity.append(capacity)

    def source_side(self, s, t):
        """Augment along shortest residual paths until no path reaches t."""
        while True:
            parent = [-1] * len(self.adj)
            parent[s] = -2
            queue = deque([s])
            while queue and parent[t] == -1:
                u = queue.popleft()
                for i in self.adj[u]:
                    v = self.head[i]
                    if self.residual[i] and parent[v] == -1:
                        parent[v] = i
                        if v == t:
                            break
                        queue.append(v)
            if parent[t] == -1:
                return np.asarray(parent) != -1
            path = []
            v = t
            while v != s:
                i = parent[v]
                path.append(i)
                v = self.head[i ^ 1]
            delta = min(self.residual[i] for i in path)
            for i in path:
                self.residual[i] -= delta
                self.residual[i ^ 1] += delta

    def certify(self, s, t, side, mixed_count):
        """Check the actual flow on original arcs, not an augmentation counter."""
        net_out = [0] * len(self.adj)
        cut = 0
        for k, capacity in enumerate(self.capacity):
            i = 2 * k
            v, u = self.head[i], self.head[i + 1]
            flow = self.residual[i + 1]
            if (type(flow) is not int or not 0 <= flow <= capacity
                    or self.residual[i] != capacity - flow):
                raise RuntimeError('invalid integral arc flow or residual capacity')
            net_out[u] += flow
            net_out[v] -= flow
            if side[u] and not side[v]:
                cut += capacity
        if not side[s] or side[t] or cut != mixed_count:
            raise RuntimeError('network cut does not certify the geometric cut')
        net_out[s] -= mixed_count
        net_out[t] += mixed_count
        if any(net_out):
            raise RuntimeError('flow does not conserve mass or match the primal value')


def minimum_middle(faces, pinned, source, target):
    """Return (flat bool middle, integer minimum); raise ValueError if infeasible.

    Each row of faces is one unit of cost if it has free links on both sides.
    The middle contains source and excludes target, and its mixed faces cannot
    be mixed by either endpoint mask. Pinned links have no label in the cut;
    their returned bits are False. Nonincident links are allowed.
    """
    faces = np.asarray(faces)
    pinned, source, target = map(np.asarray, (pinned, source, target))
    if (pinned.ndim != 1 or any(a.shape != pinned.shape or a.dtype != np.bool_
                                for a in (pinned, source, target))):
        raise ValueError('pinned, source and target must be matching flat boolean arrays')
    if faces.ndim != 2 or faces.shape[1] != 4 or faces.dtype.kind not in 'iu':
        raise ValueError('faces must be an integer array of shape (nfaces, 4)')
    n = len(pinned)
    if faces.size and (faces.min() < 0 or faces.max() >= n):
        raise ValueError('face contains an out-of-range link index')
    free = ~pinned[faces]

    def mixed(mask):
        labels = mask[faces]
        return (labels & free).any(axis=1) & (~labels & free).any(axis=1)

    def force(mask, boundary):
        forced = mask & ~pinned
        forced[faces[free & boundary[:, None]]] = True
        return forced

    sb, tb = mixed(source), mixed(target)
    left, right = force(source, sb), force(target, tb)
    if (left & right).any():
        raise ValueError('intersecting forced source and target regions')

    s = n + 2 * len(faces)
    t = s + 1
    network = _Network(t + 1)
    hard = len(faces) + 1
    for v in np.flatnonzero(left).tolist():
        network.add(s, v, hard)
    for v in np.flatnonzero(right).tolist():
        network.add(v, t, hard)
    for j, face in enumerate(faces):
        links = dict.fromkeys(face[free[j]].tolist())
        if len(links) < 2:
            continue  # no mask can split this face
        a = n + 2 * j
        network.add(a, a + 1, 1)
        for v in links:
            network.add(v, a, hard)
            network.add(a + 1, v, hard)

    side = network.source_side(s, t)
    middle = side[:n].copy()
    mb = mixed(middle)
    if ((middle & pinned).any() or (source & ~pinned & ~middle).any()
            or (target & ~pinned & middle).any() or (mb & (sb | tb)).any()):
        raise RuntimeError('middle violates an anchor or splits an endpoint boundary face')
    count = int(mb.sum())
    network.certify(s, t, side, count)
    return middle, count


def _oracle(faces, pinned, source, target):
    """Small-instance reference: enumerate masks, without expanding anchors."""
    links = set(range(len(pinned))) - set(np.flatnonzero(pinned))
    src = set(np.flatnonzero(source)) & links
    dst = set(np.flatnonzero(target)) & links
    rows = [set(row) & links for row in faces]

    def boundary(mask):
        return {j for j, row in enumerate(rows) if row & mask and row - mask}

    forbidden = boundary(src) | boundary(dst)
    best = None
    admissible = 0
    vertices = sorted(links)
    for bits in product((False, True), repeat=len(vertices)):
        mask = {v for v, bit in zip(vertices, bits) if bit}
        if src <= mask and not dst & mask:
            cut = boundary(mask)
            if not cut & forbidden:
                admissible += 1
                best = len(cut) if best is None else min(best, len(cut))
    return best, admissible


def _controls():
    # Anchors 10 and 11, and optional link 12, occur in no face. Link 9 is
    # pinned. The third row necessarily splits two versus two at cost one.
    faces = np.array([[0, 1, 2, 9], [6, 7, 8, 9], [1, 2, 6, 8],
                      [1, 3, 3, 9], [2, 4, 4, 9], [3, 4, 5, 9],
                      [5, 6, 6, 9], [4, 8, 8, 9], [9, 9, 9, 9], [3, 9, 9, 9]])
    pinned, source, target = np.zeros((3, 13), dtype=bool)
    pinned[9] = True
    source[[0, 10]] = True
    target[[7, 11]] = True
    expected, admissible = _oracle(faces, pinned, source, target)
    middle, count = minimum_middle(faces, pinned, source, target)
    if count != expected or not middle[10] or middle[11] or middle[12]:
        raise AssertionError('exhaustive minimum or isolated links disagree')
    print(f'exhaustive: admissible={admissible} min_mixed_faces={expected} certified_flow={count}')
    for x, y in product((False, True), repeat=2):
        source[9], target[9] = x, y
        other, value = minimum_middle(faces, pinned, source, target)
        if value != count or not np.array_equal(other, middle):
            raise AssertionError('pin labels changed the solution')
    print('pin labels: all endpoint labelings leave middle and cost unchanged')

    # Disjoint raw anchors, but distinct endpoint boundary faces share link 2.
    conflict = np.array([[0, 1, 2, 9], [2, 6, 7, 9]])
    if _oracle(conflict, pinned, source, target) != (None, 0):
        raise AssertionError('infeasible control has an admissible mask')
    try:
        minimum_middle(conflict, pinned, source, target)
    except ValueError as exc:
        if str(exc) != 'intersecting forced source and target regions':
            raise
        print(f'infeasible: admissible=0 rejected={exc}')
    else:
        raise AssertionError('accepted intersecting forced regions')

    # Exhaust all ternary anchor assignments for several tiny geometries,
    # with and without a pinned link, including empty and duplicate faces.
    families = [[], [[0, 1, 2, 3]], [[0, 1, 1, 1], [1, 2, 2, 2]],
                [[0, 1, 1, 1], [1, 2, 2, 2], [2, 3, 3, 3]],
                [[0, 1, 2, 3], [0, 1, 2, 3]],
                [[0, 0, 0, 0], [0, 1, 1, 1], [2, 3, 3, 3]]]
    feasible = infeasible = 0
    for rows, pin_last in product(families, (False, True)):
        tiny_faces = np.asarray(rows, dtype=int).reshape(-1, 4)
        pins = np.array([False, False, False, pin_last])
        for labels in product(range(3), repeat=4):
            labels = np.asarray(labels)
            src, dst = (labels == 1) & ~pins, (labels == 2) & ~pins
            expected, _ = _oracle(tiny_faces, pins, src, dst)
            try:
                actual, value = minimum_middle(tiny_faces, pins, src, dst)
            except ValueError:
                if expected is not None:
                    raise AssertionError('rejected an exhaustively feasible instance')
                infeasible += 1
                continue
            if expected is None or value != expected:
                raise AssertionError('minimum disagrees with exhaustive tiny oracle')
            again, repeat_value = minimum_middle(tiny_faces, pins, src, dst)
            if actual.dtype != np.bool_ or actual.shape != pins.shape:
                raise AssertionError('wrong API result type or shape')
            if not np.array_equal(again, actual) or repeat_value != value:
                raise AssertionError('nondeterministic result')
            feasible += 1
    print(f'tiny families: feasible={feasible} infeasible={infeasible} all agree with enumeration')

    # Negative certificate controls exercise every part of the lower bound.
    def certificate_network():
        graph = _Network(3)
        graph.add(0, 1, 1)
        graph.add(1, 2, 1)
        cut = graph.source_side(0, 2)
        graph.certify(0, 2, cut, 1)
        return graph, cut

    for defect in ('unit capacity', 'integrality', 'conservation', 'primal equality'):
        graph, cut = certificate_network()
        value = 1
        if defect == 'unit capacity':
            graph.residual[0:2] = [-1, 2]
        elif defect == 'integrality':
            graph.residual[0:2] = [0.5, 0.5]
        elif defect == 'conservation':
            graph.residual[2:4] = [1, 0]
        else:
            value = 0
        try:
            graph.certify(0, 2, cut, value)
        except RuntimeError:
            continue
        raise AssertionError(f'accepted defective certificate: {defect}')
    print('certificate rejection: unit capacity, integrality, conservation, primal equality')


if __name__ == '__main__':
    _controls()
