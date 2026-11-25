"""Factor samples from the degree-dependent pentanomial families with odd factor count."""

import argparse
from math import gcd, lcm
from random import Random

from flint import nmod_poly

from check_parity_sieve import residue_range, sidon


def tap_ranges(n, period):
    """Yield a smallest tap and ranges of two larger taps in the proof."""
    if n % 8 in (3, 5):
        for a in range(8, (n + 11) // 12, 8):
            scale = a // 8
            if gcd(scale, 6 * period) != 1:
                continue
            step = 4 * scale
            residue = period * (n * pow(3 * period, -1, step) % step)
            hs = residue_range(n // 4 + 1, (n + 2) // 3, residue, step * period)
            bs = range(2 * hs.start, 2 * hs.stop, 2 * hs.step)
            cs = [c for c in residue_range(3 * n // 4 + 1, n, a, 8 * period) if gcd(scale, c) == 1]
            if bs and cs:
                yield a, bs, cs
        return

    for a in range(2 if n % 8 == 0 else 8, (n + 31) // 32, 2 if n % 8 == 0 else 8):
        scale = a // (2 if n % 8 == 0 else 8)
        if gcd(scale, 6 * period) != 1:
            continue
        if n % 8 == 0:
            step = 2 * scale * period
            residue = scale * period
        elif n % 2:
            step, residue = 8 * period, 0
        else:
            step = 4 * period
            b_mod_four = 3 * (n // 2) if n % 4 == 2 else 1
            residue = period * (b_mod_four * pow(period, -1, 4) % 4)
        bs = residue_range(n // 16 + 1, (n + 7) // 8, residue, step)
        cs = residue_range(n // 4 + 1, (n + 2) // 3,
                           8 * (a * pow(8, -1, period) % period), 8 * period)
        cs = [c for c in cs if gcd(scale, c) == 1]
        if bs and cs:
            yield a, bs, cs


def check(n, cutoff, samples, random):
    period = lcm(*(2**d - 1 for d in range(1, cutoff + 1)))
    families = list(tap_ranges(n, period))
    if not families:
        raise ValueError(f"empty family in degree {n} at cutoff {cutoff}")
    tested = set()
    for a, bs, cs in families:
        for _ in range(samples):
            tested.add((0, a, random.choice(bs), random.choice(cs), n))
    for support in sorted(tested):
        if not sidon(support) or gcd(*support) != 1:
            raise ArithmeticError(f"unexpected support {support}")
        f = nmod_poly([int(i in support) for i in range(n + 1)], 2)
        factors = f.factor()[1]
        if len(factors) % 2 != 1 or any(e != 1 or g.degree() <= cutoff for g, e in factors):
            raise ArithmeticError(f"factorization failed at {support}")
    return len(tested)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=800)
    parser.add_argument("--stop", type=int, default=815)
    parser.add_argument("--cutoff", type=int, default=2)
    parser.add_argument("--samples", type=int, default=2, help="samples per admissible smallest tap")
    args = parser.parse_args()
    if not 1 <= args.start <= args.stop or min(args.cutoff, args.samples) < 1:
        parser.error("expected positive degrees, cutoff, and sample count")
    random = Random(143069)
    total = sum(check(n, args.cutoff, args.samples, random) for n in range(args.start, args.stop + 1))
    print(f"Verified all factor degrees for {total} pentanomials in degrees {args.start} to {args.stop}.")
