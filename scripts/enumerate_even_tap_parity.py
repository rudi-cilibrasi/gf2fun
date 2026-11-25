"""List exactly the odd-factor product supports with an even tap in degrees 3 or 5 modulo eight."""

import argparse


def divisor_lists(limit):
    divisors = [[] for _ in range(limit+1)]
    for d in range(1, limit+1):
        for multiple in range(d, limit+1, d):
            divisors[multiple].append(d)
    return divisors


def toggle(supports, u, v):
    pair = (u, v) if u < v else (v, u)
    if pair in supports:
        supports.remove(pair)
    else:
        supports.add(pair)


def enumerate_supports(n):
    if n < 3 or n % 8 not in (3, 5):
        raise ValueError("expected a positive degree congruent to three or five modulo eight")
    divisors = divisor_lists(2*n)
    supports = set()

    # Every contribution from a trinomial inverse has n = I*a + J*b, J >= 2.
    for m in range(2, n+1):
        for b in divisors[m]:
            j = m//b
            if j < 2 or 2*b >= n:
                break
            u = n-2*b
            choices = range(1, b) if m == n else divisors[n-m]
            for a in choices:
                if a >= b:
                    break
                r, i = b-a, (n-m)//a
                if r % 2 == 0:
                    if b % 2 == 0:
                        continue
                    left, right = i, j-2
                elif b % 2 == 0:
                    left, right = i-3, j-2
                else:
                    left, right = i, j-5
                if left >= 0 and right >= 0 and left & right == 0:
                    toggle(supports, u, 2*r)

    # The periodic terms with odd r require r to divide one of these four integers.
    for u in range(1, n-2, 2):
        b = (n-u)//2
        possible = set()
        for j in range(4):
            difference = abs(n-j*u)
            choices = divisors[difference] if difference else range(1, b, 2)
            for r in choices:
                if r >= b:
                    break
                if r % 2:
                    possible.add(r)
        for r in possible:
            a = b-r
            c = a if b % 2 == 0 else b+2*r
            k = u-c
            count = sum((n-j*u) % r == 0 for j in range(4))
            count += int(k >= 0 and k % (2*r) == 0) + int(k >= a and (k-a) % r == 0)
            if count % 2:
                toggle(supports, u, 2*r)

    # Counting each tap in turn supplies the four divisor indicators for two even taps.
    for v in range(2, n, 2):
        for choices in (divisors[n], divisors[n-v]):
            for a in choices:
                u = 2*a
                if u+v >= n:
                    break
                if u != v:
                    toggle(supports, u, v)
    return supports


def compare(n, supports):
    from check_product_parity_sector import even_taps, first_taps, sector_odd

    reference = {(min(u, v), max(u, v))
                 for u in first_taps(n, "even-tap") for v in even_taps(n, u, "even-tap")
                 if sector_odd(n, u, v)}
    if supports != reference:
        raise ArithmeticError("divisor enumeration and direct sector test disagree")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int)
    parser.add_argument("--list", action="store_true", help="write all surviving tap pairs as CSV")
    parser.add_argument("--compare", action="store_true", help="compare with every support; requires python-flint")
    args = parser.parse_args()
    if args.degree < 3 or args.degree % 8 not in (3, 5):
        parser.error("the degree must be positive and congruent to three or five modulo eight")
    result = enumerate_supports(args.degree)
    if args.compare:
        compare(args.degree, result)
    if args.list:
        print("degree,u,v")
        for u, v in sorted(result):
            print(f"{args.degree},{u},{v}")
    else:
        both = sum(u % 2 == v % 2 == 0 for u, v in result)
        print(f"Degree {args.degree}: {len(result):,} odd-factor supports with an even tap, "
              f"including {both:,} with two even taps.")
