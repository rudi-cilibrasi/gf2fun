#pragma once

#include <NTL/GF2XFactoring.h>
#include <array>
#include <cstdint>
#include <stdexcept>
#include <vector>

namespace pentanomial_1229 {
constexpr int degree = 1229;
using Word = std::uint64_t;
using Positions = std::array<Word, (degree + 63) / 64>;

struct SmallFactor {
    std::array<unsigned short, degree + 1> powers{};
    std::vector<Positions> positions;

    SmallFactor(int modulus, int d) : positions(1 << d) {
        int remainder = 1;
        for (int i = 0; i <= degree; ++i) {
            powers[i] = remainder;
            if (i < degree) positions[remainder][i / 64] |= Word(1) << (i % 64);
            remainder <<= 1;
            if (remainder >> d) remainder ^= modulus;
        }
    }
};

inline std::vector<SmallFactor> small_factors() {
    std::vector<SmallFactor> result;
    for (int d = 2; d <= 10; ++d) {
        for (int mask = (1 << d) + 1; mask < (2 << d); mask += 2) {
            NTL::GF2X f;
            for (int j = 0; j <= d; ++j)
                if ((mask >> j) & 1) NTL::SetCoeff(f, j);
            if (NTL::IterIrredTest(f)) result.emplace_back(mask, d);
        }
    }
    if (result.size() != 224) throw std::runtime_error("incomplete small-factor enumeration");
    return result;
}

struct Counts {
    std::int64_t supports = 0, tested = 0;
};

// Visit one member of each reciprocal pair that survives the small-factor sieve.
template <class Visit>
Counts visit_tap(int a, const std::vector<SmallFactor> &factors, Visit visit) {
    Counts result;
    for (int b = a + 1; b < degree - a; ++b) {
        // Keep the smaller of (a,b,c) and (n-c,n-b,n-a) in lexicographic order.
        const int cmax = degree - a - (2 * b > degree ? 1 : 0);
        if (b >= cmax) continue;
        result.supports += cmax - b;
        const int first = (b + 1) / 64, last = cmax / 64;
        Positions excluded{};
        for (const auto &g : factors) {
            const int residue = 1 ^ g.powers[degree] ^ g.powers[a] ^ g.powers[b];
            for (int w = first; w <= last; ++w)
                excluded[w] |= g.positions[residue][w];
        }
        for (int w = first; w <= last; ++w) {
            Word candidates = ~excluded[w];
            if (w == first) candidates &= ~Word(0) << ((b + 1) % 64);
            if (w == last) candidates &= ~Word(0) >> (63 - cmax % 64);
            while (candidates) {
                const int c = 64 * w + __builtin_ctzll(candidates);
                candidates &= candidates - 1;
                ++result.tested;
                visit(b, c);
            }
        }
    }
    return result;
}
}
