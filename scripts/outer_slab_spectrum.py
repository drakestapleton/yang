"""CPU diagnostic for the radius-one slab in replica_shell_probe (not a sampler)."""
import numpy as np


COLUMNS = ('identity', 'four_min', 'rigid_min', 'rigid_max', 'site_min_sum', 'face_min_sum',
           'sites_straddling_zero')


def _dot_form(a, b):
    """Matrix of q -> a dot (q b q^-1) on unit quaternions (Euclidean dot)."""
    x, y = a[..., 1:], b[..., 1:]
    xy = (x*y).sum(axis=-1)
    m = np.empty((*xy.shape, 4, 4))
    m[..., 0, 0] = xy
    m[..., 1:, 0] = m[..., 0, 1:] = np.cross(y, x)
    outer = x[..., :, None]*y[..., None, :]
    m[..., 1:, 1:] = outer + outer.swapaxes(-1, -2) - xy[..., None, None]*np.eye(3)
    return m + (a[..., 0]*b[..., 0])[..., None, None]*np.eye(4)


def measure(lat, u, beta, verify, mul, inv):
    """Min/max of the signed field before tanh; local extrema are relaxations only."""
    frame = lat.tree_frame(u, lat.layers, verify)
    mask = lat.masks['slab'][1]
    # Each crossing temporal plaquette has a lone spatial link at its top.
    sites = lat.sites[mask[0] != mask[0, lat.plus[3]]]
    forms = []
    for i in range(3):
        top = frame[:, i, lat.plus[3, sites]]
        path = mul(mul(inv(frame[:, 3, sites]), frame[:, i, sites]),
                   frame[:, 3, lat.plus[i, sites]])
        before = (path*top).sum(axis=(0, 2))
        crossed = _dot_form(path[0], top[1]) + _dot_form(top[0], path[1])
        forms.append((beta/2)*(before[:, None, None]*np.eye(4)-crossed))
    face = np.stack(forms)
    # U(1) allows only q in the real-i plane, not arbitrary SU(2) conjugators.
    dim = 2 if lat.group == 'U1' else 4
    face = face[..., :dim, :dim]
    site = face.sum(axis=0)
    whole = site.sum(axis=0)
    eig, vec = np.linalg.eigh(whole)
    site_eig = np.linalg.eigvalsh(site)
    if verify:
        # Both extremizers and a generic off-axis orientation against the *full*
        # rotated/swapped Wilson action, without reusing the crossing-face formula.
        before = lat.traces(frame).sum()
        generic = np.arange(1, dim+1, dtype=float)
        for v in (vec[:, 0], vec[:, -1], generic/np.linalg.norm(generic)):
            q = np.pad(v, (0, 4-dim))
            rotated = frame.copy()
            rotated[1] = mul(mul(q, frame[1]), inv(q))
            swapped = np.where(mask[None, ..., None], rotated[::-1], rotated)
            direct = beta*(before-lat.traces(swapped).sum())/2
            np.testing.assert_allclose(v @ whole @ v, direct, atol=1e-9, rtol=0)
        if dim == 2:
            np.testing.assert_allclose(face, face[..., :1, :1]*np.eye(2), atol=1e-12, rtol=0)
    return (whole[0, 0], whole.diagonal().min(), eig[0], eig[-1], site_eig[:, 0].sum(),
            np.linalg.eigvalsh(face)[..., 0].sum(), ((site_eig[:, 0]<0) & (site_eig[:, -1]>0)).sum())
