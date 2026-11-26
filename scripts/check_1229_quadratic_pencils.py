"""Count nonsplit Artin–Schreier fibers on all projective F_1024-sublines of F_(2^20)."""

from collections import Counter

from check_1229_hermitian_descent import F, Q, bits, scalar_groups


def circle_counts():
    torus, real = scalar_groups()
    basis = [F.gen() ** i for i in range(20)]
    masks = [bits(t) for t in torus]
    counts = Counter()
    for scale in real[1:]:
        # Evaluate Tr(scale * t) as a binary linear form in the coefficients of t.
        functional = sum(int((scale * z).trace()) << i for i, z in enumerate(basis))
        nonsplit = sum((functional & t).bit_count() % 2 for t in masks)
        # Half the translations have trace zero. The other half exchange the two counts.
        counts[nonsplit] += Q**2 // 2
        counts[Q + 1 - nonsplit] += Q**2 // 2
    return counts


def main():
    try:
        counts = circle_counts()
    finally:
        scalar_groups.cache_clear()
    if sum(counts.values()) != Q**2 * (Q-1) or (min(counts), max(counts)) != (481, 544):
        raise ArithmeticError("incomplete list of finite norm circles")
    print(f"Norm circles have {min(counts)} to {max(counts)} nonsplit quadratic fibers.")
    # There are q+1 affine directions. One is horizontal, with q possible translates.
    counts[0] += Q // 2
    counts[Q] += Q // 2
    counts[Q // 2] += Q**2
    if sum(counts.values()) != Q**3 + Q or counts[0] != Q // 2:
        raise ArithmeticError("incorrect projective subline census")
    minimum = min(n for n in counts if n)
    print(f"Of {Q**3 + Q:,} projective sublines, {counts[0]} split everywhere. "
          f"The others contain at least {minimum} nonsplit quadratic fibers.")


if __name__ == "__main__":
    main()
