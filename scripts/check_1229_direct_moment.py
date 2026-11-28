"""Verify the 4,944-input direct order criterion for Seroussi's degree-1229 pentanomial.

Use --targets to emit the requested masks. Pass one or more mask,exponent CSV
files with --logs to verify full powers, or add --projected to check K-th powers.
Requires python-flint and sympy.
"""

import argparse
import csv
import sys
from collections import Counter
from fractions import Fraction
from math import gcd
from pathlib import Path

from check_1229_wheel import EXTENDED_BOUND
from check_degree_1229 import COFACTOR, GROUP, KNOWN, check_known_order
from check_factor_base import (DATA, irreducible, irreducible_counts, modulus, moment_bound,
                               polynomial, seroussi_identities, seroussi_relations, verify_logs)


# Reflect at the last entry. Divide entries of odd index by sqrt(2) in the moment formula.
HALF_WEIGHTS = (
    486, 1421, 1409, 2443, 1984, 3104, 2373, 3576, 2671, 3970, 2946, 4376,
    3260, 4887, 3692, 5638, 4266, 6375, 4720, 6942, 5082, 7415, 5399, 7852,
    5707, 8296, 6033, 8780, 6392, 9309, 6773, 9830, 7114, 10274, 7406, 10664,
    7671, 11028, 7924, 11383, 8175, 11739, 8427, 12092, 8670, 12423, 8890,
    12711, 9079, 12961, 9245, 13184, 9396, 13387, 9534, 13575, 9660, 13743,
    9771, 13885, 9860, 13995, 9925, 14071, 9968, 14118, 9992, 14139, 10000,
)
WEIGHTS = HALF_WEIGHTS + HALF_WEIGHTS[-2::-1]


def score(counts):
    return moment_bound(counts, EXTENDED_BOUND + 1, len(WEIGHTS) - 1, weights=WEIGHTS)


def requested_masks():
    with (DATA / 'degree-1229-seroussi-direct-targets.csv').open() as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != ['mask', 'degree']:
            raise ValueError('expected mask,degree columns')
        masks = []
        for row in reader:
            p = int(row['mask'])
            if int(row['degree']) != p.bit_length() - 1 or not irreducible(polynomial(p)):
                raise ValueError(f'invalid target {p}')
            masks.append(p)
    if masks != sorted(set(masks)) or len(masks) != 4944:
        raise ValueError('invalid direct-certificate inputs')
    return masks


def verify_criterion(f, masks):
    if not irreducible(f):
        raise ArithmeticError('reducible sparse modulus')
    check_known_order(f)
    counts = irreducible_counts(15)
    counts[16] = 228
    bound = score(counts)
    expected = Fraction(356112683324172380993987964422215087730554819995787,
                        290229303099191540429874230304885944987852734464)
    if bound != expected or bound <= 1227:
        raise ArithmeticError('insufficient moment bound')
    # Conditional closure. No logarithm is assumed to have been computed here.
    have = {2, *masks}
    for terms, _ in seroussi_identities(f):
        missing = terms.keys() - have
        if len(missing) != 1:
            raise ArithmeticError('a folded identity does not isolate a single factor')
        p, = missing
        if gcd(terms[p], GROUP) != 1:
            raise ArithmeticError('the isolated coefficient is not invertible')
        have.add(p)
    actual = Counter(p.bit_length() - 1 for p in have)
    if actual != counts | {18: 1, 612: 1}:
        raise ArithmeticError('the requested masks do not reconstruct the stated degree counts')
    print(f'Conditional certificate verified. {len(masks)} supplied logarithms suffice, Q = {float(bound):.9f}.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--targets', action='store_true')
    action.add_argument('--logs', nargs='+', type=Path, help='verify one or more mask,exponent CSV files')
    parser.add_argument('--projected', action='store_true', help='verify powers projected by the known factor K')
    args = parser.parse_args()
    if args.projected and not args.logs:
        parser.error('--projected applies to --logs')
    masks = requested_masks()
    if args.targets:
        writer = csv.writer(sys.stdout, lineterminator='\n')
        writer.writerow(('mask', 'degree'))
        writer.writerows((p, p.bit_length() - 1) for p in masks)
        return
    f = modulus(1229, (2, 6, 15))
    verify_criterion(f, masks)
    if args.logs:
        projection = KNOWN if args.projected else 1
        if gcd(KNOWN, COFACTOR) != 1:
            raise ArithmeticError('overlapping components of the group order')
        logs = verify_logs(args.logs, 1229, f, projection=projection)
        seroussi_relations(logs, f, projection=projection)
        bound = score(Counter(p.bit_length() - 1 for p in logs))
        print(f'{len(logs)} verified values including derived powers. Actual moment bound {float(bound):.9f}.')
        if bound > 1227:
            print('The supplied powers prove that the pentanomial is primitive.')


if __name__ == '__main__':
    main()
