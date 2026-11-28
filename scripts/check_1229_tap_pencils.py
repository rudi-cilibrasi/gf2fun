"""Count common failure pairs that differ by a single tap and verify the sharp coloring bound."""

import argparse
import csv
import gzip
from collections import Counter, defaultdict, deque
from itertools import combinations
from math import comb

from check_1229_joint_codes import CAPACITY, DATA, DEGREE, check_field_powers


def representative(taps):
    return min(taps, tuple(DEGREE - t for t in reversed(taps)))


def census():
    supports = []
    anchors = []
    pencils = defaultdict(list)
    with gzip.open(DATA / "degree-1229-irreducible-supports.csv.gz", "rt", newline="") as stream:
        for row in csv.DictReader(stream):
            if int(row["missing_mask"]):
                continue
            taps = representative(tuple(int(row[k]) for k in "abc"))
            keys = sorted({representative(pair) for pair in combinations(taps, 2)})
            for key in keys:
                pencils[key].append(len(supports))
            supports.append(taps)
            anchors.append(keys)
    if len(supports) != 319572 or len(set(supports)) != len(supports):
        raise ArithmeticError("incorrect number of distinct surviving reciprocal classes")
    return supports, anchors, pencils


def check(list_members):
    supports, anchors, pencils = census()
    large = {k: group for k, group in pencils.items() if len(group) > CAPACITY}
    histogram = Counter(map(len, large.values()))
    if histogram != {15: 15, 16: 6, 17: 4, 18: 2, 19: 1}:
        raise ArithmeticError("incorrect distribution of pencils larger than fourteen")
    fixed = (263, 483)
    third_taps = []
    for i in large[fixed]:
        taps = supports[i]
        if not set(fixed).issubset(taps):
            taps = tuple(DEGREE - t for t in reversed(taps))
        third, = set(taps) - set(fixed)
        third_taps.append(third)
    if sorted(third_taps) != [299, 334, 359, 520, 564, 570, 641, 733, 753, 769,
                              792, 877, 916, 919, 985, 1077, 1089, 1196, 1216]:
        raise ArithmeticError("the 19 single-tap choices differ")
    incidences = Counter(i for group in large.values() for i in group)
    shared, = (i for i, count in incidences.items() if count > 1)
    if len(incidences) != 443 or incidences[shared] != 2 or supports[shared] != (284, 630, 914):
        raise ArithmeticError("unexpected overlap of the large pencils")
    excess = sum((size - CAPACITY)*count for size, count in histogram.items())
    pairs = sum(comb(size, 2)*count for size, count in histogram.items())
    if (excess, pairs) != (52, 3316):
        raise ArithmeticError("incorrect number of forced collisions or eligible pairs")
    if list_members:
        print("anchor_a,anchor_b,representative_a,representative_b,representative_c")
        for key, group in sorted(large.items()):
            for i in group:
                print(*key, *supports[i], sep=",")

    def neighbors(i):
        result = {j for key in anchors[i] for j in pencils[key]}
        result.remove(i)
        return result

    # Precolor the endpoints of all edges between different large pencils,
    # and their one shared member. Distinct colors here prevent extra collisions.
    pinned = set(incidences)
    special = {shared}
    for i in pinned:
        for j in neighbors(i) & pinned:
            if i < j and not any(k in large and k in anchors[j] for k in anchors[i]):
                special.update((i, j))
    if len(special) > CAPACITY:
        raise ArithmeticError("too many endpoints to precolor distinctly")
    colors = [-1] * len(supports)
    for color, i in enumerate(sorted(special)):
        colors[i] = color
    erased = {shared}
    palette = set(range(CAPACITY))
    for key, group in sorted(large.items()):
        seen = {colors[i] for i in group if colors[i] >= 0}
        free = iter(i for i in group if colors[i] < 0)
        for color in sorted(palette - seen):
            colors[next(free)] = color
        # Give each surplus vertex a different second copy of a color.
        # In both pencils containing the shared vertex, double its color first.
        repeats = sorted(palette, key=lambda c: (c != colors[shared], c))
        for i, color in zip(free, repeats):
            colors[i] = color
            if shared not in group or color != colors[shared]:
                erased.add(i)

    # A vertex removed with at most 13 remaining neighbors can always be
    # colored when put back. Leave all 443 precolored vertices in place.
    degree = [len(neighbors(i)) for i in range(len(supports))]
    if sum(degree) != 2*1496102:
        raise ArithmeticError("incorrect number of adjacent reciprocal pairs")
    pending = deque(i for i, d in enumerate(degree) if i not in pinned and d < CAPACITY)
    removed = []
    while pending:
        i = pending.popleft()
        removed.append(i)
        for j in neighbors(i):
            if j not in pinned:
                degree[j] -= 1
                if degree[j] == CAPACITY - 1:
                    pending.append(j)
    if len(removed) + len(pinned) != len(supports):
        raise ArithmeticError("uncolored vertices survive the deletion process")
    for i in reversed(removed):
        colors[i] = min(palette - {colors[j] for j in neighbors(i)})
    if any(c not in palette for c in colors):
        raise ArithmeticError("incomplete coloring")
    collisions = {(i, j) for i in range(len(supports)) for j in neighbors(i)
                  if i < j and colors[i] == colors[j]}
    if len(collisions) != 52 or len(erased) != 51 or any(
            i not in erased and j not in erased for i, j in collisions):
        raise ArithmeticError("coloring or 51-vertex deletion does not attain the lower bound")
    print("The 28 large pencils have 443 distinct members and 3,316 distinct pairs. "
          "Every 14-coloring has at least 52 adjacent pairs of equal color. "
          "A checked coloring of all 319,572 survivors attains 52, and deleting 51 vertices "
          "removes every collision.")
    return {supports[i] for i in pinned}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--field", action="store_true", help="also replay all 443 field witnesses")
    parser.add_argument("--list-members", action="store_true", help="list the 28 families by tap pair")
    args = parser.parse_args()
    members = check(args.list_members)
    if args.field:
        check_field_powers(members)
