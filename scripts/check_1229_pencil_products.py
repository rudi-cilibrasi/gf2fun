"""Verify common-field roots and every known-prime cancellation among degree-1229 pencil products."""

import argparse
import csv
import json
from collections import Counter, defaultdict, deque
from itertools import combinations
from math import comb, gcd

from check_1229_joint_codes import CAPACITY
from check_degree_1229 import COFACTOR, GROUP, KNOWN, N, PRIMES
from check_factor_base import DATA, modulus, polynomial


TAPS = (299, 334, 359, 520, 564, 570, 641, 733, 753, 769,
        792, 877, 916, 919, 985, 1077, 1089, 1196, 1216)


def read_roots():
    data = json.loads((DATA/'degree-1229-pencil-roots.json').read_text())
    model = json.loads((DATA/'degree-1229-q1024-certificate.json').read_text())
    if data['model_q'] != 1024 or data['fixed_taps'] != [263, 483]:
        raise ValueError("incorrect pencil or field")
    f = polynomial(int(model['modulus_hex'], 16))
    x = polynomial(2)
    if f.degree() != N or f(0) == 0 or f(1) == 0 or x.pow_mod(1 << N, f) != x:
        raise ArithmeticError("the degree-1229 model modulus is reducible")
    roots = {}
    for row in data['roots']:
        c = row['tap']
        mask = int(row['root_hex'], 16)
        if c in roots or not 1 < mask < 1 << N:
            raise ValueError("invalid pencil root")
        root = polynomial(mask)
        if modulus(N, [263, 483, c]).compose_mod(root, f) != 0:
            raise ArithmeticError(f"incorrect common-field root at tap {c}")
        if type(row['use_inverse']) is not bool:
            raise ValueError("invalid reciprocal orientation")
        roots[c] = root.xgcd(f)[1] % f if row['use_inverse'] else root
    if tuple(sorted(roots)) != TAPS:
        raise ValueError("incorrect pencil members")
    return f, roots


def known_cancellations(f, roots):
    # The first entry is the certified primitive element X in the dense model.
    # A label (sign,h) describes the product a_i * a_j^(sign*2^h), i<j.
    elements = [polynomial(2)] + [roots[c] for c in TAPS]
    pencil_labels = Counter()
    anchor_labels = Counter()
    per_prime = []
    for p in PRIMES:
        projected = [a.pow_mod(GROUP//p, f) for a in elements]
        if any(v == 1 for v in projected):
            raise ArithmeticError(f"a listed element misses the prime {p}")
        inverse = [v.pow_mod(p-1, f) for v in projected]
        hits = 0
        for j in range(1, len(elements)):
            v = projected[j]
            for h in range(N):
                for i in range(j):
                    if v == projected[i]:
                        sign = -1
                    elif v == inverse[i]:
                        sign = 1
                    else:
                        continue
                    if i == 0:
                        anchor_labels[sign, h] += 1
                    else:
                        pencil_labels[sign, h] += 1
                        hits += 1
                v = v*v % f
            if v != projected[j]:
                raise ArithmeticError("Frobenius did not close")
        per_prime.append(hits)
    if per_prime != [8, 6, 0, 0] or pencil_labels != {(-1, 0): 13, (1, 472): 1}:
        raise ArithmeticError(f"unexpected pencil cancellations: {pencil_labels}, {per_prime}")
    if anchor_labels != {(-1, 764): 2, (-1, 1201): 2}:
        raise ArithmeticError(f"unexpected cancellations with the generator: {anchor_labels}")
    common = 2*N - CAPACITY*comb(len(roots), 2) - len(pencil_labels)
    anchored = 2*N - CAPACITY*len(roots) - len(anchor_labels)
    print(f"Known cancellation counts {per_prime}. The 171 pairs use only {dict(pencil_labels)}. "
          f"At least {common} signed Frobenius shifts realize every pairwise lcm simultaneously.")
    print(f"Generator products: {len(anchor_labels)} distinct known cancellation shifts "
          f"{dict(anchor_labels)}; at least {anchored} shifts make all 19 products primitive.")


def check_relative(path, projected, target, f):
    # Each edge gives the difference of two unknown logarithms. The common
    # offset cancels throughout a connected component of verified edges.
    neighbors = defaultdict(list)
    with open(path, newline='') as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != ['tap_a', 'tap_b', 'exponent']:
            raise ValueError("expected tap_a,tap_b,exponent")
        for row in reader:
            a, b, e = (int(row[key]) for key in reader.fieldnames)
            if a not in projected or b not in projected or a == b:
                raise ValueError("expected two distinct pencil taps")
            if projected[a]*target.pow_mod(e % COFACTOR, f) % f != projected[b]:
                raise ArithmeticError(f"invalid relative logarithm for {a}, {b}")
            neighbors[a].append((b, e))
            neighbors[b].append((a, -e))

    unseen = set(neighbors)
    while unseen:
        first = min(unseen)
        offsets = {first: 0}
        queue = deque([first])
        while queue:
            a = queue.popleft()
            for b, difference in neighbors[a]:
                value = (offsets[a] + difference) % COFACTOR
                if b not in offsets:
                    offsets[b] = value
                    queue.append(b)
                elif offsets[b] != value:
                    raise ArithmeticError("inconsistent relative logarithms")
        unseen.difference_update(offsets)
        for a, b in combinations(sorted(offsets), 2):
            divisor = gcd(offsets[a]-offsets[b], COFACTOR)
            if divisor > 1:
                if divisor == COFACTOR:
                    raise ArithmeticError("distinct projected roots have the same logarithm")
                print(f"Taps {a}, {b} give a proper divisor of the remaining cofactor: {divisor}.")
                break
        else:
            print(f"All offset differences are units for taps {sorted(offsets)}. "
                  f"At least {max(0, len(offsets)-CAPACITY)} of these pentanomials are primitive.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--relative', metavar='CSV', help='also verify submitted relative logarithms')
    args = parser.parse_args()
    field, members = read_roots()
    projected = {c: r.pow_mod(KNOWN, field) for c, r in members.items()}
    if any(v == 1 for v in projected.values()) or any(
            projected[a] == projected[b] for a, b in combinations(TAPS, 2)):
        raise ArithmeticError("cofactor projections must be nonidentity and pairwise distinct")
    known_cancellations(field, members)
    if args.relative:
        check_relative(args.relative, projected, polynomial(2).pow_mod(KNOWN, field), field)
