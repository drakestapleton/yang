"""Reduce each hot/cold chain separately. All losses are base-ten log fractions."""
import csv
from itertools import groupby
import sys

import numpy as np


def summarize(rows):
    for key, group in groupby(rows, lambda r: tuple(r[k] for k in
            ('group', 'side', 'warmup', 'samples', 'stride', 'beta', 'start', 'seed'))):
        group = list(group)
        if [int(r['sample']) for r in group] != list(range(int(key[3]))):
            raise ValueError('incomplete or reordered sample series')
        def col(name):
            return np.array([float(r[name]) for r in group])
        source = np.abs(np.tanh(col('source_j')))
        if 'narrow1_j' in group[0]:
            families = (('narrow1', 'narrow2'), ('wide1', 'wide2'))
        elif 'radius1_j' in group[0]:
            families = (('radius1', 'radius2'),)
        else:
            families = (('cut',), ('slab',))
        for family in families:
            w = source
            for name in family:
                counts = col(name+'_faces')
                if not np.all(counts == counts[0]):
                    raise ValueError('geometry changed in chain')
                j = col(name+'_j')
                live = w > 0
                if live.any():
                    lognum = np.log(w[live])+np.log(2.)-np.logaddexp(0., 2*np.abs(j[live]))
                    logsum = np.logaddexp.reduce(lognum)
                    loss = (logsum-np.log(w.sum()))/np.log(10.)
                    largest_share = np.exp(lognum.max()-logsum)
                else:
                    loss = largest_share = float('nan')  # No surviving preceding weight.
                print(key[0], key[5], key[6], len(j), name, int(counts[0]), f'{j.min():.8g}',
                      f'{j.max():.8g}', f'{loss:.8g}', f'{largest_share:.8g}')
                if name != family[-1]:
                    w = w * np.abs(np.tanh(j))


if __name__ == '__main__':
    print('group beta start pairs middle split_faces min_J max_J log10_loss largest_loss_share')
    for path in sys.argv[1:]:
        with open(path) as f:
            summarize(csv.DictReader(f, delimiter='\t'))
