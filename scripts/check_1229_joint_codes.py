"""Check the degree-1229 common-failure coding threshold and the optimal disjoint tap packing."""

import argparse
import csv
import gzip
import json
from collections import Counter, defaultdict
from itertools import combinations
from math import comb
from pathlib import Path


DATA = Path(__file__).resolve().parents[1] / "data"
DEGREE = 1229
CAPACITY = 14


def folded_taps(taps):
    """Identify a tap with its position in the reciprocal polynomial."""
    return tuple(sorted({min(t, DEGREE-t) for t in taps}))


def balanced_pairs(members):
    small, larger_classes = divmod(members, CAPACITY)
    return CAPACITY*comb(small, 2) + larger_classes*small


def check_field_powers(witness):
    from check_degree_1229 import GROUP, PRIMES
    from check_factor_base import modulus, polynomial

    x = polynomial(2)
    for taps in sorted(witness):
        f = modulus(DEGREE, taps)
        # The degree is prime. The pentanomial has no linear factor, so
        # divisibility by X^(2^1229)-X is equivalent to irreducibility.
        if x.pow_mod(1 << DEGREE, f) != x:
            raise ArithmeticError(f"reducible packing member {taps}")
        if any(x.pow_mod(GROUP//p, f) == 1 for p in PRIMES):
            raise ArithmeticError(f"packing member {taps} fails a known prime test")
    print(f"Independently verified irreducibility and all four order tests on {len(witness)} members.")


def check(replay):
    certificate = json.loads((DATA/'degree-1229-disjoint-tap-packing.json').read_text())
    cover = set(certificate['mixed_edge_cover'])
    witness = {tuple(taps) for taps in certificate['supports']}
    if len(witness) != 240 or len(cover) != 39:
        raise ValueError("incorrect packing or mixed-edge cover size")
    selected = set()
    used = set()
    incidences = [Counter() for _ in range(4)]
    shapes = Counter()
    known = defaultdict(list)
    survivors = 0
    active = {v for v in range(1, (DEGREE+1)//2) if v % 4 in (2, 3)}
    with gzip.open(DATA/'degree-1229-irreducible-supports.csv.gz', 'rt', newline='') as source:
        for row in csv.DictReader(source):
            taps = tuple(int(row[k]) for k in 'abc')
            labels = folded_taps(taps)
            mask = int(row['missing_mask'])
            if mask:
                known[mask].append(set(labels))
                continue
            survivors += 1
            active_count = len(active.intersection(labels))
            shape = (len(labels), active_count)
            shapes[shape] += 1
            if active_count == 0 or len(labels) not in (2, 3):
                raise ArithmeticError(f"unsupported tap pattern at {taps}")
            if shape == (2, 1) and cover.isdisjoint(labels):
                raise ArithmeticError(f"mixed edge at {taps} escapes its cover")
            for k in range(1, len(labels)+1):
                incidences[k].update(combinations(labels, k))
            if taps in witness:
                if not used.isdisjoint(labels):
                    raise ArithmeticError("two selected supports share a folded tap")
                selected.add(taps)
                used.update(labels)
    if survivors != 319572 or selected != witness or used != set(range(1, 615)):
        raise ArithmeticError("the packing does not partition all tap positions into surviving supports")
    if len(active) != 307 or shapes[(2, 1)] != 74 or shapes[(2, 2)] != 676:
        raise ArithmeticError("the two-label support counts differ")
    if (614+307+len(cover))//4 != len(selected):
        raise ArithmeticError("packing and upper bound differ")
    if len(selected)-CAPACITY*2**4 != 16:
        raise ArithmeticError("incorrect four-bit bound within the packing")
    moments = [sum(comb(v, 2) for v in counts.values()) for counts in incidences[1:]]
    if moments != [772030772, 2688440, 1333]:
        raise ArithmeticError("incorrect common-tap incidence counts")
    sharing = moments[0]-moments[1]+moments[2]
    forced = balanced_pairs(survivors)-sharing
    if sharing != 769343665 or forced != 2877863093:
        raise ArithmeticError("incorrect number of forced disjoint common failures")
    maximum_bad = survivors-33784
    if not balanced_pairs(maximum_bad) <= (1 << 31)+sharing < balanced_pairs(maximum_bad+1):
        raise ArithmeticError("incorrect 31-bit joint code threshold")
    common = [a.isdisjoint(b) for group in known.values() for a, b in combinations(group, 2)]
    if {m: len(group) for m, group in known.items()} != {1: 5, 2: 6} or len(common) != 25 or not all(common):
        raise ArithmeticError("the 25 known same-prime pairs must have disjoint folded taps")
    print(f"{sharing:,} of {comb(survivors, 2):,} unordered survivor pairs share a folded tap.")
    print(f"A counterexample forces at least {forced:,} disjoint-tap pairs with a common failed prime.")
    print("A 31-bit index for those pairs implies at least 33,784 primitive reciprocal pairs.")
    print(f"The maximum packing has {len(selected)} supports and uses all {len(used)} folded taps.")
    if replay:
        check_field_powers(selected)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--field', action='store_true', help='also replay the 1,200 field powers with FLINT')
    check(parser.parse_args().field)
