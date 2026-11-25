// Count degree-1229 pentanomials dividing X^K+1, up to reciprocal pairs.
#include <NTL/GF2XFactoring.h>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
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

std::vector<SmallFactor> small_factors() {
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
    std::int64_t supports = 0, tested = 0, divisors = 0;
};

Counts check_tap(int a, const std::vector<SmallFactor> &factors, const NTL::ZZ &order) {
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
                NTL::GF2X f, power;
                for (int i : {0, a, b, c, degree}) NTL::SetCoeff(f, i);
                NTL::PowerXMod(power, order, NTL::GF2XModulus(f));
                ++result.tested;
                if (NTL::IsOne(power)) {
                    ++result.divisors;
                    #pragma omp critical
                    std::cerr << "divisor " << a << ' ' << b << ' ' << c << '\n';
                }
            }
        }
    }
    return result;
}
}

int main(int argc, char **argv) {
    int first = 1, last = degree / 2;
    if (argc == 3) {
        first = std::stoi(argv[1]);
        last = std::stoi(argv[2]);
    }
    if ((argc != 1 && argc != 3) || first < 1 || last < first || last > degree / 2) {
        std::cerr << "usage: check_1229_known_subgroup [first_tap last_tap]\n";
        return 2;
    }
    const NTL::ZZ order = NTL::conv<NTL::ZZ>("9536289355314392579996071515160583098298616686033085857")
                        * NTL::conv<NTL::ZZ>("10543179280661916121033") * 36871 * 46703;
    const auto factors = small_factors();
    // Store shards in tap order even if several threads finish out of order.
    std::vector<Counts> results(last - first + 1);
    #pragma omp parallel for schedule(dynamic, 1)
    for (int a = first; a <= last; ++a)
        results[a - first] = check_tap(a, factors, order);
    std::cout << "smallest_tap,supports,power_tests,divisors\n";
    for (int a = first; a <= last; ++a) {
        const auto &row = results[a - first];
        std::cout << a << ',' << row.supports << ',' << row.tested << ',' << row.divisors << '\n';
    }
}
