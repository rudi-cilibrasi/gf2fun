// Check the four-column minors at the small residual lengths for degrees 7*q^b.
// The Python verifier supplies the order-q Frobenius generator and the short triple.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Masks = std::vector<std::uint8_t>;

int add_mod(int a, int b, int ell) {
    int sum = a + b;
    return sum < ell ? sum : sum - ell;
}

int mul_mod(int a, int b, int ell) {
    return static_cast<int>(static_cast<std::int64_t>(a) * b % ell);
}

// Each bit corresponds to one coset of <2>. At exponent zero the trace is one,
// which is also the sum of the six unknown period traces.
Masks classify(int ell) {
    Masks classes(ell);
    classes[0] = 63;
    int count = 0;
    for (int first = 1; first < ell; ++first) {
        if (classes[first]) continue;
        if (count == 6) throw std::runtime_error("more than six binary cosets");
        int x = first, length = 0;
        do {
            classes[x] = 1U << count;
            ++length;
            x = add_mod(x, x, ell);
        } while (x != first);
        if (6 * length != ell - 1 || length % 2 == 0)
            throw std::runtime_error("unexpected binary coset length");
        ++count;
    }
    if (count != 6) throw std::runtime_error("fewer than six binary cosets");
    return classes;
}

// For a fourth column c, expand the 4-by-4 determinant along that column.
// Entry x in each table is the sum of six trace masks with that offset.
std::array<Masks, 4> cofactor_tables(const Masks &classes,
                                     const std::array<int, 4> &rows, int i, int j) {
    int ell = static_cast<int>(classes.size());
    std::array<Masks, 4> tables;
    for (int omitted = 0; omitted < 4; ++omitted) {
        auto &table = tables[omitted];
        table.resize(ell);
        for (int a = 0; a < 4; ++a) {
            for (int b = 0; b < 4; ++b) {
                if (a == omitted || b == omitted || a == b) continue;
                int offset = add_mod(mul_mod(rows[a], i, ell), mul_mod(rows[b], j, ell), ell);
                for (int x = 0; x < ell; ++x) {
                    table[x] ^= classes[offset];
                    if (++offset == ell) offset = 0;
                }
            }
        }
    }
    return tables;
}

int main() {
    int ell, q, generator, i, j;
    if (!(std::cin >> ell >> q >> generator >> i >> j) || ell < 7 || ell > 30000000 ||
        q < 5 || q >= ell || generator <= 1 || generator >= ell ||
        i <= 0 || i >= j || j > 6)
        throw std::runtime_error("invalid length, relative generator or triple");
    int order = 1, power = generator;
    while (power != 1 && order < q) {
        power = mul_mod(power, generator, ell);
        ++order;
    }
    if (order != q || power != 1) throw std::runtime_error("incorrect relative order");
    const auto classes = classify(ell);

    // A set bit is a still possible assignment of the six period traces.
    // Their sum is one. A trace of zero retains the assignments orthogonal to the mask.
    std::array<std::uint32_t, 64> orthogonal{};
    int assignment = 0;
    for (unsigned t = 1; t < 64; ++t) {
        if (!__builtin_parity(t)) continue;
        for (unsigned mask = 0; mask < 64; ++mask)
            if (!__builtin_parity(t & mask)) orthogonal[mask] |= std::uint32_t(1) << assignment;
        ++assignment;
    }
    const std::array<int, 4> rows{1, generator, mul_mod(generator, generator, ell),
                                  mul_mod(mul_mod(generator, generator, ell), generator, ell)};
    const auto tables = cofactor_tables(classes, rows, i, j);
    std::array<int, 4> offsets{};
    int max_shifts = 0;
    for (int c = 0; c < ell; ++c) {
        if (c != 0 && c != i && c != j) {
            std::uint32_t possible = UINT32_MAX;
            auto shifted = offsets;
            int shifts = 0;
            while (possible && shifts < std::min(ell, 256)) {
                unsigned mask = 0;
                for (int r = 0; r < 4; ++r) {
                    mask ^= tables[r][shifted[r]];
                    if (++shifted[r] == ell) shifted[r] = 0;
                }
                possible &= orthogonal[mask];
                ++shifts;
            }
            if (possible) {
                std::cerr << "Inconclusive at fourth column " << c << '\n';
                return 1;
            }
            max_shifts = std::max(max_shifts, shifts);
        }
        for (int r = 0; r < 4; ++r) offsets[r] = add_mod(offsets[r], rows[r], ell);
    }
    std::cout << ell << ' ' << i << ' ' << j << ' ' << ell - 3 << ' ' << max_shifts << '\n';
}
