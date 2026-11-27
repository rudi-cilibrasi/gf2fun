// Find an irreducible X^n + X^c + X^b + X^a + 1, searching an interval of c.
// If 2^n-1 is prime the result is primitive. Replay the order separately.
#include <NTL/GF2XFactoring.h>

#include <algorithm>
#include <charconv>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string_view>
#include <utility>
#include <vector>

namespace {
using NTL::GF2X;
using Word = std::uint32_t;

long positive_integer(std::string_view text) {
    long value;
    auto end = text.data() + text.size();
    auto parsed = std::from_chars(text.data(), end, value);
    if (parsed.ec != std::errc{} || parsed.ptr != end || value < 1 ||
        value > std::numeric_limits<int>::max())
        throw std::invalid_argument("expected a positive 32-bit integer");
    return value;
}

struct TrialFactor {
    Word fixed;
    std::vector<Word> powers;
};

std::vector<TrialFactor> trial_factors(long n, long high) {
    std::vector<TrialFactor> factors;
    for (int degree = 2; degree <= 16 && degree < n; ++degree) {
        const Word leading = Word(1) << degree;
        for (Word mask = leading+1; mask < 2*leading; mask += 2) {
            GF2X polynomial;
            for (int j = 0; j <= degree; ++j)
                if ((mask >> j) & 1) NTL::SetCoeff(polynomial, j);
            if (!NTL::IterIrredTest(polynomial)) continue;
            const GF2X residue = NTL::PowerXMod(n, NTL::GF2XModulus(polynomial));
            Word fixed = 1;
            for (int j = 0; j < degree; ++j)
                if (NTL::IsOne(NTL::coeff(residue, j))) fixed ^= Word(1) << j;
            TrialFactor factor{fixed, std::vector<Word>(high+1)};
            factor.powers[0] = 1;
            for (long j = 1; j <= high; ++j) {
                Word next = factor.powers[j-1] << 1;
                factor.powers[j] = next & leading ? next ^ mask : next;
            }
            factors.push_back(std::move(factor));
        }
    }
    return factors;
}

int search(int argc, char** argv) {
    if (argc != 4 && argc != 5)
        throw std::invalid_argument("usage: search_low_pentanomials DEGREE FIRST_HIGH LAST_HIGH [MIDDLE]");
    long n = positive_integer(argv[1]);
    long first = positive_integer(argv[2]), last = positive_integer(argv[3]);
    long middle = argc == 5 ? positive_integer(argv[4]) : 0;
    if (first < 3 || last < first || n <= last || (middle && (middle < 2 || middle >= last)))
        throw std::invalid_argument("expected 3 <= FIRST_HIGH <= LAST_HIGH < DEGREE and 2 <= MIDDLE < LAST_HIGH");
    auto factors = trial_factors(n, last);
    for (long c = first; c <= last; ++c) {
        long last_middle = middle ? std::min(middle, c-1) : c-1;
        for (long b = middle ? middle : 2; b <= last_middle; ++b) {
            for (long a = 1; a < b; ++a) {
                bool divides = std::any_of(factors.begin(), factors.end(), [=](const TrialFactor& f) {
                    return (f.powers[a] ^ f.powers[b] ^ f.powers[c]) == f.fixed;
                });
                if (divides) continue;
                GF2X candidate;
                for (long tap : {0L, a, b, c, n}) NTL::SetCoeff(candidate, tap);
                if (NTL::IterIrredTest(candidate)) {
                    std::cout << n << ',' << a << ',' << b << ',' << c << '\n';
                    return 0;
                }
            }
        }
    }
    std::cerr << "No irreducible pentanomial in the requested tap range.\n";
    return 1;
}
}  // namespace

int main(int argc, char** argv) {
    try { return search(argc, argv); }
    catch (const std::exception& error) { std::cerr << error.what() << '\n'; return 2; }
}
