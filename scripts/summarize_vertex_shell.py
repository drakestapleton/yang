"""Summarize recorded --vertex-shell TSVs without treating correlated rows as IID."""
import csv
import sys
from itertools import groupby

import numpy as np


def summarize(rows):
    def col(name):
        return np.array([float(r[name]) for r in rows])

    inner, outer, witness, lower = map(col, ('inner_j', 'outer_j', 'witness_j', 'dual_lower_j'))
    fixed = np.stack([outer, col('checker_j'), col('pattern_j'), col('pattern_checker_j')])
    weight, cancel, logloss = map(col, ('inner_abs', 'weighted_cancellation', 'log_weighted_loss'))
    # Decision buffer applies to signs, not to the measure of a neighborhood.
    eps = 1e-8
    assert np.all(lower <= witness+eps) and np.all(witness <= outer+eps)
    positive = fixed.max(axis=0) > eps
    negative = np.minimum(witness, fixed.min(axis=0)) < -eps
    crosses = positive & negative
    excludes = lower > eps
    assert not np.any(negative & excludes)
    np.testing.assert_allclose(np.abs(np.tanh(inner)), weight, atol=1e-10, rtol=0)
    np.testing.assert_allclose(col('weighted_mean_abs')-col('weighted_abs_mean'), cancel, atol=1e-10, rtol=0)
    assert not np.isnan(logloss).any() and np.all(logloss <= 1e-9)
    if weight.sum():
        log_fraction = (np.logaddexp.reduce(logloss)-np.log(weight.sum()))/np.log(10.)
        gain = cancel.sum()/weight.sum()
    else:
        log_fraction = gain = float('nan')  # no remaining product to normalize
    return (len(rows), crosses.sum(), excludes.sum(), (~(crosses|excludes)).sum(),
            (positive & (fixed.min(axis=0)<-eps)).sum(), gain, log_fraction)


if __name__ == '__main__':
    print('group beta start n witness_cross dual_positive unresolved fixed_cross cancellation_fraction log10_loss_fraction')
    for path in sys.argv[1:]:
        with open(path) as f:
            for key, group in groupby(csv.DictReader(f, delimiter='\t'), lambda r: (r['group'], r['beta'], r['start'])):
                print(*key, *(f'{x:.9g}' for x in summarize(list(group))))
