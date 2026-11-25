// Exhaustively check irreducibility and the five available order projections in degree 1229.
#include "pentanomial_1229_supports.hpp"
#include <algorithm>
#include <iostream>
#include <string>
#if defined(__PCLMUL__)
#include <wmmintrin.h>
#endif

namespace {
using namespace pentanomial_1229;
constexpr int words = (degree + 63) / 64;
constexpr int top_bits = degree % 64;
using Element = std::array<Word, words>;
using Exponents = std::array<NTL::ZZ, 5>;

#if !defined(__PCLMUL__)
// Insert zeroes between adjacent bits of a 32-bit word.
Word spread(std::uint32_t bits) {
    Word v = bits;
    v = (v | (v << 16)) & 0x0000ffff0000ffffULL;
    v = (v | (v << 8))  & 0x00ff00ff00ff00ffULL;
    v = (v | (v << 4))  & 0x0f0f0f0f0f0f0f0fULL;
    v = (v | (v << 2))  & 0x3333333333333333ULL;
    return (v | (v << 1)) & 0x5555555555555555ULL;
}
#endif

class SparseModulus {
    std::array<int, 3> offsets, shifts, gaps;

    // One exponent bit sends v to v^2 or X*v^2. Squared monomials have even degree.
    template<bool feedback>
    void step(Element &v, bool times_x) const {
        std::array<Word, 2*words + 1> buffer{};
        for (int i = 0; i < words; ++i) {
#if defined(__PCLMUL__)
            const __m128i t = _mm_cvtsi64_si128(v[i]);
            __m128i square = _mm_clmulepi64_si128(t, t, 0);
            if (times_x) square = _mm_slli_epi64(square, 1);
            _mm_storeu_si128(reinterpret_cast<__m128i *>(buffer.data() + 2*i), square);
#else
            buffer[2*i] = spread(static_cast<std::uint32_t>(v[i])) << times_x;
            buffer[2*i+1] = spread(static_cast<std::uint32_t>(v[i] >> 32)) << times_x;
#endif
        }
        for (int i = words-1; i >= 0; --i) {
            Word h = (buffer[i+words-1] >> top_bits) | (buffer[i+words] << (64-top_bits));
            // A tap within 63 places of the leading term can feed the current block.
            // Invert 1+U modulo T^64 using (1+U)(1+U^2)(1+U^4)... in characteristic two.
            if constexpr (feedback) {
                for (int scale = 1; scale*gaps[2] < 64; scale *= 2) {
                    Word correction = 0;
                    for (int gap : gaps)
                        if (scale*gap < 64) correction ^= h >> (scale*gap);
                    h ^= correction;
                }
            }
            // Replace h*X^(degree+64*i) by h*X^(64*i)*(1+X^a+X^b+X^c).
            // The high block is discarded and is never read in a later iteration.
            buffer[i] ^= h;
            for (int j = 0; j < 3; ++j) {
                buffer[i+offsets[j]] ^= h << shifts[j];
                if (shifts[j]) buffer[i+offsets[j]+1] ^= h >> (64-shifts[j]);
            }
        }
        std::copy_n(buffer.begin(), words, v.begin());
        v.back() &= (Word(1) << top_bits)-1;
    }

    template<bool feedback>
    Element power_bits(const NTL::ZZ &exponent) const {
        Element v{1};
        for (int j = NTL::NumBits(exponent)-1; j >= 0; --j) step<feedback>(v, NTL::bit(exponent, j));
        return v;
    }
public:
    SparseModulus(int a, int b, int c)
        : offsets{a/64, b/64, c/64}, shifts{a%64, b%64, c%64}, gaps{degree-a, degree-b, degree-c} {}

    Element power(const NTL::ZZ &exponent) const {
        return gaps[2] < 64 ? power_bits<true>(exponent) : power_bits<false>(exponent);
    }

    bool irreducible() const {
        const Element x{2};
        Element v = x;
        if (gaps[2] < 64) {
            for (int j = 0; j < degree; ++j) step<true>(v, false);
        } else {
            for (int j = 0; j < degree; ++j) step<false>(v, false);
        }
        // Since 1229 is prime and all supports avoid 0 and 1 as roots,
        // a degree-1229 divisor of X^(2^1229)+X is irreducible.
        return v == x;
    }
};

Exponents order_tests() {
    const NTL::ZZ group = NTL::power2_ZZ(degree)-1;
    const std::array<NTL::ZZ, 4> primes = {
        NTL::to_ZZ(36871), NTL::to_ZZ(46703), NTL::conv<NTL::ZZ>("10543179280661916121033"),
        NTL::conv<NTL::ZZ>("9536289355314392579996071515160583098298616686033085857")
    };
    Exponents tests;
    tests[4] = 1;
    for (int i = 0; i < 4; ++i) {
        tests[i] = group/primes[i];
        tests[4] *= primes[i];
    }
    return tests;
}

void verify_arithmetic(const Exponents &tests) {
    const std::array<std::array<int, 3>, 6> cases = {{
        {2,6,15}, {27,50,77}, {64,128,1152}, {1,1167,1228}, {2,1224,1227}, {609,614,620}
    }};
    for (auto taps : cases) {
        SparseModulus packed(taps[0], taps[1], taps[2]);
        NTL::GF2X f;
        for (int i : {0, taps[0], taps[1], taps[2], degree}) NTL::SetCoeff(f, i);
        if (packed.irreducible() != static_cast<bool>(NTL::IterIrredTest(f)))
            throw std::runtime_error("irreducibility disagrees with NTL");
        const NTL::GF2XModulus modulus(f);
        for (const auto &e : tests) {
            const auto v = packed.power(e);
            const auto check = NTL::PowerXMod(e, modulus);
            for (int i = 0; i < degree; ++i)
                if (((v[i/64] >> (i%64)) & 1) != NTL::IsOne(NTL::coeff(check, i)))
                    throw std::runtime_error("packed power disagrees with NTL");
        }
    }
}

struct Result {
    Counts counts;
    long irreducibles = 0;
    std::array<long, 32> missing{};
    std::vector<std::array<int, 3>> taps;
};

Result check(int a, const std::vector<SmallFactor> &factors, const Exponents &tests, bool list) {
    Result r;
    r.counts = visit_tap(a, factors, [&](int b, int c) {
        const SparseModulus f(a, b, c);
        if (!f.irreducible()) return;
        ++r.irreducibles;
        int missing = 0;
        for (int j = 0; j < 5; ++j)
            if (f.power(tests[j]) == Element{1}) missing |= 1 << j;
        ++r.missing[missing];
        if (missing || list) r.taps.push_back({b, c, missing});
    });
    return r;
}
}

int main(int argc, char **argv) {
    const bool list = argc > 1 && std::string(argv[1]) == "--list";
    const int arg = list ? 2 : 1;
    int first = 1, last = degree/2;
    if (argc == arg+2) {
        first = std::stoi(argv[arg]);
        last = std::stoi(argv[arg+1]);
    }
    if ((argc != arg && argc != arg+2) || first < 1 || last < first || last > degree/2) {
        std::cerr << "usage: census_1229_pentanomials [--list] [first_tap last_tap]\n";
        return 2;
    }
    const auto tests = order_tests();
    verify_arithmetic(tests);
    const auto factors = small_factors();
    std::vector<Result> results(last-first+1);
    #pragma omp parallel for schedule(dynamic, 1)
    for (int a = first; a <= last; ++a) results[a-first] = check(a, factors, tests, list);
    if (list) {
        std::cout << "a,b,c,missing_mask\n";
        for (int a = first; a <= last; ++a)
            for (auto row : results[a-first].taps)
                std::cout << a << ',' << row[0] << ',' << row[1] << ',' << row[2] << '\n';
        return 0;
    }
    std::cout << "smallest_tap,supports,no_small_factor,irreducibles,all_five,missing_p1,missing_p2,missing_both,other\n";
    std::cerr << "a,b,c,missing_mask\n";
    for (int a = first; a <= last; ++a) {
        const auto &r = results[a-first];
        std::cout << a << ',' << r.counts.supports << ',' << r.counts.tested << ',' << r.irreducibles;
        long other = r.irreducibles;
        for (int i = 0; i < 4; ++i) {
            std::cout << ',' << r.missing[i];
            other -= r.missing[i];
        }
        std::cout << ',' << other << '\n';
        for (auto row : r.taps)
            std::cerr << a << ',' << row[0] << ',' << row[1] << ',' << row[2] << '\n';
    }
}
