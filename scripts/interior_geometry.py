"""Two sharp interior cuts between whole spatial slices on the pinned side-eight torus."""
import numpy as np


def interior_geometry(lat, pinned):
    """Free-link masks: source plaquette, radius 1, radius 2, target plaquette."""
    n = lat.sites.size
    if n != 8**4 or pinned.shape != (4, n) or pinned.dtype != np.bool_:
        raise ValueError('expected a side-eight lattice and its boolean tree pins')
    free = ~pinned.ravel()
    time = lat.sites % 8  # time is the last coordinate in C site order
    radius = np.tile(np.minimum(time, 8-time), 4)

    def endpoint(site):
        mask = np.zeros_like(free)
        mask[lat.faces[lat.pairs.index((0, 1)), site]] = True
        return mask & free

    target = np.ravel_multi_index((0, 0, 0, 4), (8,)*4)
    return endpoint(0), (radius <= 1) & free, (radius <= 2) & free, endpoint(target)


def _boundary(lat, pinned, mask):
    faces = lat.faces.reshape(-1, 4)
    active = ~pinned.ravel()[faces]
    labels = mask[faces]
    return (active & labels).any(axis=1) & (active & ~labels).any(axis=1)


def _tree_pins(lat, side):
    coords = np.array(np.unravel_index(lat.sites, (side,)*4))
    child = lat.sites[1:]
    direction = np.argmax(coords[:, child] != 0, axis=0)
    parent = lat.minus[direction, child]
    assert np.all(coords[:, parent].sum(axis=0) == coords[:, child].sum(axis=0)-1)
    pinned = np.zeros((4, lat.sites.size), dtype=bool)
    pinned[direction, parent] = True
    assert pinned.sum() == lat.sites.size-1
    return pinned


def _packing(lat, pinned, side, separation):
    """Enumerate free-link paths and actual face IDs on both temporal arcs."""
    n = lat.sites.size
    paths = []
    per_direction = []
    for direction in range(3):
        bases = lat.sites[(lat.sites % side == 0) & ~pinned[direction]]
        per_direction.append(len(bases))
        plane = lat.pairs.index((direction, 3))
        for base in bases:
            for step, length in ((1, separation), (-1, side-separation)):
                sites = [int(base)]
                face_ids = []
                for _ in range(length):
                    old = sites[-1]
                    new = int((lat.plus if step == 1 else lat.minus)[3, old])
                    face_site = old if step == 1 else new
                    face_ids.append(plane*n+face_site)
                    sites.append(new)
                links = direction*n+np.array(sites)
                face_ids = np.array(face_ids)
                assert not pinned.ravel()[links].any()
                assert sites[0] % side == 0 and sites[-1] % side == separation
                rows = lat.faces.reshape(-1, 4)[face_ids]
                assert np.all((rows == links[:-1, None]).any(axis=1))
                assert np.all((rows == links[1:, None]).any(axis=1))
                paths.append((links, face_ids))
    all_faces = np.concatenate([faces for _, faces in paths])
    assert len(np.unique(all_faces)) == len(all_faces)
    assert any(np.any(faces % n % side == side-1) for _, faces in paths)
    assert len(paths) == 2*(2*side**3+1)
    return paths, per_direction


def _controls():
    from replica_shell_probe import Lattice

    lat = Lattice(8, 'SU2')
    pinned = _tree_pins(lat, 8)
    masks = interior_geometry(lat, pinned)
    n = lat.sites.size
    assert isinstance(masks, tuple) and len(masks) == 4
    assert all(m.dtype == np.bool_ and m.shape == (4*n,) for m in masks)
    assert all(not (m & pinned.ravel()).any() for m in masks)
    source, inner, outer, target = masks
    assert source.any() and target.any() and not (source & target).any()
    assert (source <= inner).all() and (inner <= outer).all()
    assert not (outer & target).any()
    boundaries = [_boundary(lat, pinned, m) for m in masks]
    assert np.max(np.sum(boundaries, axis=0)) == 1
    paths, per_direction = _packing(lat, pinned, 8, 4)
    slice0 = np.tile(lat.sites % 8 == 0, 4) & ~pinned.ravel()
    slice4 = np.tile(lat.sites % 8 == 4, 4) & ~pinned.ravel()
    slice0[3*n:] = False
    slice4[3*n:] = False
    faces = lat.faces.reshape(-1, 4)
    for mask, boundary in zip((inner, outer), boundaries[1:3]):
        assert mask[slice0].all() and not mask[slice4].any()
        assert boundary.sum() == len(paths)
        witnesses = []
        for links, face_ids in paths:
            assert mask[links[0]] and not mask[links[-1]]
            split = mask[links[:-1]] != mask[links[1:]]
            assert split.sum() == 1 and boundary[face_ids[split]].all()
            witnesses.extend(face_ids[split])
        np.testing.assert_array_equal(np.sort(witnesses), np.flatnonzero(boundary))
        # Inspect actual vertices, including link heads, rather than base times.
        row = faces[boundary]
        directions, bases = row//n, row % n
        times = np.concatenate((bases.ravel() % 8,
                                lat.plus[directions, bases].ravel() % 8))
        assert not np.isin(times, (0, 4)).any()
        sheets = np.unique((np.flatnonzero(boundary) % n) % 8).tolist()
        print(f'interior: faces={int(boundary.sum())} lower_base_times={sheets} '
              f'vertex_times={np.unique(times).tolist()} paths_hit_once={len(witnesses)}')
    endpoint_spatial = []
    for time in (0, 4):
        vertices = np.flatnonzero(slice0 if time == 0 else slice4)
        adjacency = {int(v): set() for v in vertices}
        face_ids = np.concatenate([
            i*n+lat.sites[lat.sites % 8 == time]
            for i, pair in enumerate(lat.pairs) if 3 not in pair])
        endpoint_spatial.extend(face_ids)
        for row in faces[face_ids]:
            free_row = row[~pinned.ravel()[row]]
            for link in free_row:
                adjacency[int(link)].update(map(int, free_row))
        seen = set()
        components = 0
        for vertex in adjacency:
            if vertex in seen:
                continue
            components += 1
            queue = [vertex]
            seen.add(vertex)
            while queue:
                for neighbor in adjacency[queue.pop()]:
                    if neighbor not in seen:
                        seen.add(neighbor)
                        queue.append(neighbor)
        assert components == 1 and len(seen) == len(vertices)
        anchor = source if time == 0 else target
        assert np.count_nonzero(anchor[vertices]) == 1
        print(f'endpoint_spatial_graph: time={time} vertices={len(vertices)} '
              f'components={components} local_anchor_count={int(anchor[vertices].sum())}')
    print(f'side8: free_spatial_per_direction={per_direction} '
          f'path_count={len(paths)} boundary_counts={[int(b.sum()) for b in boundaries]} '
          'all_four_boundaries_pairwise_disjoint=True wraparound_checked=True')

    # Endpoint separation (even with boundary collars) is a weaker class.
    local = source.copy()
    touched = faces[boundaries[0]].ravel()
    local[touched] = ~pinned.ravel()[touched]
    local_boundary = _boundary(lat, pinned, local)
    assert local[source].all() and not local[target].any()
    assert not (local_boundary & (boundaries[0] | boundaries[3])).any()
    assert local_boundary.sum() < len(paths) and not local[slice0].all()
    assert local_boundary[np.array(endpoint_spatial)].any()
    print(f'wrong_class: endpoint_collar_faces={int(local_boundary.sum())} '
          'endpoint_separates=True endpoint_boundaries_disjoint=True '
          'whole_source_slice_contained=False endpoint_spatial_face_split=True')

    # Direct enumeration of the finite general formula, including odd sides,
    # adjacent endpoints, unequal arc lengths, and the periodic seam.
    for side, separation, radius in ((4, 1, 0), (5, 2, 0), (6, 3, 1), (8, 4, 2)):
        test = Lattice(side, 'SU2')
        pins = _tree_pins(test, side)
        packing, free_counts = _packing(test, pins, side, separation)
        time = test.sites % side
        slab = np.tile(np.minimum(time, side-time) <= radius, 4) & ~pins.ravel()
        boundary = _boundary(test, pins, slab)
        assert boundary.sum() == len(packing)
        for links, face_ids in packing:
            assert slab[links[0]] and not slab[links[-1]]
            assert boundary[face_ids].sum() == 1
        print(f'general: side={side} separation={separation} radius={radius} '
              f'free_spatial_per_direction={free_counts} sharp_faces={int(boundary.sum())}')
    print('PASS: geometry only; no configuration generation or field measurement')


if __name__ == '__main__':
    _controls()
