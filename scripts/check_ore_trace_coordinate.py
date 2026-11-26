"""Verify the trace-hyperplane power maps between reciprocal binary Ore lifts."""

import argparse
import json
import subprocess
from math import gcd
from pathlib import Path

from check_cubed_parity import X, polynomial
from check_ore_logarithms import ore_power_table
from check_ore_norms import support
from make_witnesses import primitive, square_mod
from period_coordinate import mask_of


DATA = Path(__file__).resolve().parents[1] / "data" / "degree-2047-ore-coordinate.json"


def trace_exponent(seed):
    s = seed.bit_length() - 1
    if s < 2:
        raise ValueError("use a primitive seed of degree at least two")
    trace_mask = 0
    for i in range(s):
        value = 1 << i
        trace = 0
        for _ in range(s):
            trace ^= value
            value = square_mod(value, seed)
        if trace not in (0, 1):
            raise ValueError("the binary trace escaped the base field")
        trace_mask |= trace << i
    return sum(1 << j for value, j in ore_power_table(seed).items()
               if (value & trace_mask).bit_count() % 2 == 0)


def coordinate(seed):
    s = seed.bit_length() - 1
    n = (1 << s) - 1
    size = (1 << n) - 1
    reverse = sum(1 << (s - i) for i in support(seed))
    exponent = trace_exponent(seed)
    reverse_exponent = trace_exponent(reverse)
    reversed_bits = sum(1 << (-j % n) for j in support(exponent))
    if exponent.bit_count() != (1 << (s - 1)) - 1 or reverse_exponent != reversed_bits:
        raise ArithmeticError("incorrect trace hyperplanes or reversed indices")
    for k in range(1, n):
        shift = ((exponent << k) & size) | (exponent >> (n - k))
        if (exponent & shift).bit_count() != (1 << (s - 2)) - 1:
            raise ArithmeticError("incorrect hyperplane intersection")
    if exponent * reverse_exponent % size != 1 << (s - 2):
        raise ArithmeticError("the trace powers do not compose to the predicted Frobenius")
    inverse = (reverse_exponent << (n - (s - 2))) % size
    if inverse * exponent % size != 1:
        raise ArithmeticError("the power map is not invertible")

    source, target = (polynomial((1 << i) - 1 for i in support(p)) for p in (seed, reverse))
    y_in_x = X.pow_mod(exponent, source)
    x_in_y = X.pow_mod(inverse, target)
    if (not source.is_irreducible() or not target.is_irreducible()
            or target.compose_mod(y_in_x, source) != 0 or source.compose_mod(x_in_y, target) != 0
            or x_in_y.compose_mod(y_in_x, source) != X or y_in_x.compose_mod(x_in_y, target) != X):
        raise ArithmeticError("the polynomial substitution maps are not inverse field isomorphisms")
    return {
        "degree": n,
        "source_seed_hex": hex(seed),
        "target_seed_hex": hex(reverse),
        "source_taps": list(support(mask_of(source))),
        "target_taps": list(support(mask_of(target))),
        "y_as_power_of_x_hex": hex(exponent),
        "x_as_power_of_y_hex": hex(inverse),
        "y_as_polynomial_in_x_hex": hex(mask_of(y_in_x)),
        "x_as_polynomial_in_y_hex": hex(mask_of(x_in_y)),
    }


def trace_power_census(executable, jobs):
    seeds = [p for p in range(2049, 4096, 2) if primitive(11, p, (23, 89))]
    exponents = [trace_exponent(p) for p in seeds]
    if (len(seeds) != 176 or len(set(exponents)) != 176
            or any(gcd(e, (1 << 2047) - 1) != 1 for e in exponents)):
        raise ArithmeticError("incomplete seed or trace-power enumeration")
    request = "".join(f"{p} {e}\n" for p, e in zip(seeds, exponents))
    result = subprocess.run([executable, str(jobs)], input=request, text=True,
                            check=True, stdout=subprocess.PIPE)
    off_diagonal = []
    sparse = 0
    for seed, line in zip(seeds, result.stdout.splitlines(), strict=True):
        source, *weights = map(int, line.split())
        if source != seed:
            raise ArithmeticError("incorrect source seed")
        for target, weight in zip(seeds, weights, strict=True):
            if target == seed and weight != seed.bit_count():
                raise ArithmeticError("incorrect reciprocal lift weight")
            if target != seed:
                off_diagonal.append((weight, source, target))
            sparse += weight <= 5
    low, high = min(off_diagonal), max(off_diagonal)
    sparse_source_low = min(w for w, p, _ in off_diagonal if p.bit_count() <= 5)
    if (sparse != 46 or low != (941, 0xb6f, 0xb65) or high != (1121, 0xb5f, 0x949)
            or sparse_source_low != 945):
        raise ArithmeticError("incorrect weight extrema or sparse-image count")
    return low, high, sparse


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=lambda value: int(value, 0), default=0x805)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--emit", action="store_true", help="emit the checked coordinate in JSON")
    action.add_argument("--census", metavar="EXECUTABLE", help="check all degree-2047 trace powers with NTL")
    parser.add_argument("--jobs", type=int, default=1, help="thread count for the NTL census")
    args = parser.parse_args()
    if args.census:
        low, high, sparse = trace_power_census(args.census, args.jobs)
        print(f"176 by 176 trace powers: {sparse} sparse images; "
              f"off-diagonal minimum (weight, source, seed) {low}, maximum {high}")
    else:
        result = coordinate(args.seed)
        if args.emit:
            print(json.dumps(result, indent=2))
        else:
            if args.seed == 0x805 and result != json.loads(DATA.read_text()):
                raise ArithmeticError("the published degree-2047 coordinates differ")
            print(f"degree {result['degree']}: both trace exponents and both field substitutions verified")
