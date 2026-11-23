"""Compare total incoming weight lost over both shells, on matched replica pairs."""
import argparse
import csv
from itertools import groupby

import numpy as np

CHAIN = ('group', 'side', 'warmup', 'samples', 'stride', 'beta', 'start', 'seed')
SHARED = (*CHAIN, 'sample', 'source_faces', 'target_faces', 'source_j', 'target_j')


def compare(local, interior):
    pairs = zip(local, interior, strict=True)
    for key, chain in groupby(pairs, lambda pair: tuple(pair[0][k] for k in CHAIN)):
        rows = list(chain)
        if [int(a['sample']) for a, _ in rows] != list(range(int(key[3]))):
            raise ValueError('incomplete or reordered local sample series')
        if any(a[k] != b[k] for a, b in rows for k in SHARED):
            raise ValueError('neighborhood and whole-slice pairs do not match')
        def field(side, name):
            return np.array([float(pair[side][name+'_j']) for pair in rows])
        a = abs(np.tanh(field(0, 'source')))
        live = a > 0
        values = []
        for side, first, second in ((0,'narrow1','narrow2'), (0,'wide1','wide2'),
                                    (1,'radius1','radius2')):
            if not live.any():
                values.append(float('nan'))
                continue
            b, c = (abs(field(side, k)[live]) for k in (first, second))
            # 1 - BC = (1 - B) + B(1 - C). Keep both terms even if B rounds to one.
            log_first = np.log(2.)-np.logaddexp(0., 2*b)
            with np.errstate(divide='ignore'):
                log_second = np.log(np.tanh(b))+np.log(2.)-np.logaddexp(0., 2*c)
            loss = np.log(a[live])+np.logaddexp(log_first, log_second)
            values.append((np.logaddexp.reduce(loss)-np.log(a.sum()))/np.log(10.))
        yield key, values


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('local', type=argparse.FileType('r'))
    parser.add_argument('interior', type=argparse.FileType('r'))
    args = parser.parse_args()
    print('group beta start pairs log10_joint_narrow log10_joint_wide log10_joint_slices')
    for key, values in compare(*(csv.DictReader(f, delimiter='\t') for f in (args.local, args.interior))):
        print(key[0], key[5], key[6], key[3], *(f'{x:.9g}' for x in values))
