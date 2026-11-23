"""Compare a --haar-shell run to the corresponding archived --vertex-shell pairs."""
import argparse
import csv
from itertools import groupby

import numpy as np


PAIR = ('group', 'side', 'warmup', 'samples', 'stride', 'beta', 'start', 'seed', 'sample')


def summarize(rows, prior):
    def paired():
        for row, ref in zip(rows, prior, strict=True):
            if any(row[k] != ref[k] for k in PAIR):
                raise ValueError('different chains or sample order')
            for field in ('inner_j', 'outer_j'):
                np.testing.assert_allclose(float(row[field]), float(ref[field]), atol=2e-9, rtol=2e-11)
            yield row

    for key, batch in groupby(paired(), lambda r: (r['group'], r['beta'], r['start'])):
        batch = list(batch)
        def col(k):
            return np.array([float(r[k]) for r in batch])
        a = np.abs(np.tanh(col('inner_j')))
        with np.errstate(divide='ignore'):
            log_a = np.log(a)
        def weighted_log10(log_values):
            if not a.any():
                return float('nan')  # preceding weight is zero
            return (np.logaddexp.reduce(log_a + log_values) - np.log(a.sum())) / np.log(10.)
        draws, neg = col('draws'), col('negative')
        # Haar symmetry makes |E tanh(C+X)| <= tanh(|C|) exactly.
        log_floor = np.log(2.) - np.logaddexp(0., 2*np.abs(col('center')))
        print(*key, len(a), int(draws.sum()), int(neg.sum()), f'{weighted_log10(log_floor):.8g}',
              *(f'{weighted_log10(col(k)):.8g}' for k in ('log_p_upper', 'log_loss_upper', 'log_draw_loss')))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('haar', type=argparse.FileType('r'))
    parser.add_argument('vertex', type=argparse.FileType('r'))
    args = parser.parse_args()
    print('group beta start pairs draws negative log10_weighted_loss_floor log10_weighted_p_ceiling log10_weighted_loss_ceiling log10_weighted_draw_loss')
    summarize(*(csv.DictReader(f, delimiter='\t') for f in (args.haar, args.vertex)))
