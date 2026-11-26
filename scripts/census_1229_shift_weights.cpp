// Find every degree-1229 irreducible pentanomial with a translate of weight at most 33.
#include <NTL/GF2XFactoring.h>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

namespace {
constexpr int n = 1229;
constexpr int bound = 33;
using Mask = std::array<std::uint64_t, (n + 64) / 64>;

std::array<Mask, n+1> translated_powers() {
    std::array<Mask, n+1> powers{};
    powers[0][0] = 1;
    for (int i = 1; i <= n; ++i) {
        std::uint64_t carry = 0;
        for (size_t k = 0; k < powers[i].size(); ++k) {
            const auto u = powers[i-1][k];
            powers[i][k] = u ^ (u << 1) ^ carry;
            carry = u >> 63;
        }
    }
    return powers;
}

Mask add(const Mask& a, const Mask& b) {
    Mask result;
    for (size_t k = 0; k < result.size(); ++k) result[k] = a[k] ^ b[k];
    return result;
}

int shift_weight(const Mask& prefix, const Mask& last) {
    int count = 0;
    for (size_t k = 0; k < prefix.size() && count <= bound; ++k)
        count += __builtin_popcountll(prefix[k] ^ last[k]);
    return count;
}

struct Slice {
    std::array<int, bound+1> weights{};
    std::vector<std::array<int, 4>> irreducibles;
};
}

int main() {
    const auto powers = translated_powers();
    const Mask endpoints = add(powers[n], powers[0]);
    std::vector<Slice> slices(n);
    #pragma omp parallel for schedule(dynamic, 2)
    for (int a = 1; a < n-2; ++a) {
        const Mask first = add(endpoints, powers[a]);
        for (int b = a+1; b < n-1; ++b) {
            const Mask prefix = add(first, powers[b]);
            for (int c = b+1; c < n; ++c) {
                int w = shift_weight(prefix, powers[c]);
                if (w > bound) continue;
                ++slices[a].weights[w];
                NTL::GF2X f;
                for (int i : {0, a, b, c, n}) NTL::SetCoeff(f, i);
                if (NTL::IterIrredTest(f)) slices[a].irreducibles.push_back({a,b,c,w});
            }
        }
    }
    std::array<int, bound+1> counts{};
    std::cout << "a,b,c,translated_weight\n";
    for (const auto& slice : slices) {
        for (int w = 0; w <= bound; ++w) counts[w] += slice.weights[w];
        for (auto [a,b,c,w] : slice.irreducibles)
            std::cout << a << ',' << b << ',' << c << ',' << w << '\n';
    }
    for (int w = 0; w <= bound; ++w)
        if (counts[w]) std::cerr << "weight " << w << ": " << counts[w] << " supports\n";
}
