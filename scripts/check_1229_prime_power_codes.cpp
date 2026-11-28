// Build with g++ -O3 -std=c++17 check_1229_prime_power_codes.cpp -lntl -lgmp
// Check all sums of up to six distinct elements in two prime-order subgroups.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using NTL::GF2X;
using NTL::GF2XModulus;

constexpr long degree = 1229;
constexpr long byte_count = (degree + 7) / 8;
using Coordinates = std::array<std::uint64_t, (degree + 63) / 64>;

// Coordinate i is the constant coefficient of v^(2^i) in the polynomial
// basis. Squaring rotates these bits. The maximum cyclic 64-bit window is
// exactly invariant; the census checks every possible signature collision.
class FrobeniusSignature {
    using ByteTable = std::array<Coordinates, 256>;
    std::vector<ByteTable> table;

public:
    explicit FrobeniusSignature(const GF2XModulus& modulus) : table(byte_count, ByteTable{}) {
        for (long j = 0; j < degree; ++j) {
            GF2X value;
            NTL::SetCoeff(value, j);
            auto& row = table[j / 8][1U << (j % 8)];
            for (long i = 0; i < degree; ++i) {
                if (NTL::IsOne(NTL::ConstTerm(value)))
                    row[i / 64] |= std::uint64_t{1} << (i % 64);
                NTL::SqrMod(value, value, modulus);
            }
        }
        // Precompute linear combinations one byte at a time.
        for (auto& byte : table) {
            for (unsigned mask = 1; mask < 256; ++mask) {
                unsigned bit = mask & -mask;
                if (mask == bit) continue;
                for (std::size_t j = 0; j < byte[mask].size(); ++j)
                    byte[mask][j] = byte[bit][j] ^ byte[mask ^ bit][j];
            }
        }
    }

    std::uint64_t operator()(const GF2X& value) const {
        std::array<unsigned char, byte_count> bytes;
        NTL::BytesFromGF2X(bytes.data(), value, byte_count);
        Coordinates row{};
        for (long i = 0; i < byte_count; ++i) {
            const auto& part = table[i][bytes[i]];
            for (std::size_t j = 0; j < row.size(); ++j) row[j] ^= part[j];
        }
        std::uint64_t window = 0, best = 0;
        for (long i = 0; i < degree + 63; ++i) {
            long b = i < degree ? i : i - degree;
            window = (window << 1) | ((row[b / 64] >> (b % 64)) & 1);
            if (i >= 63) best = std::max(best, window);
        }
        return best;
    }
};

static std::string field_key(const GF2X& value) {
    std::string key(byte_count, '\0');
    NTL::BytesFromGF2X(reinterpret_cast<unsigned char*>(key.data()), value, byte_count);
    return key;
}

static bool prime(long n) {
    if (n < 2) return false;
    for (long p = 2; p <= n / p; ++p)
        if (n % p == 0) return false;
    return true;
}

static void check_subgroup(long p, long expected_min_weight, const GF2XModulus& modulus,
                           const FrobeniusSignature& signature) {
    const NTL::ZZ group_order = NTL::power2_ZZ(degree) - 1;
    if (!prime(p) || group_order % p != 0) throw std::runtime_error("invalid subgroup order");
    GF2X generator = NTL::PowerXMod(group_order / p, modulus);
    if (NTL::IsOne(generator) || !NTL::IsOne(NTL::PowerMod(generator, p, modulus)))
        throw std::runtime_error("generator has incorrect order");
    std::vector<GF2X> powers(p);
    NTL::set(powers[0]);
    for (long i = 1; i < p; ++i) NTL::MulMod(powers[i], powers[i-1], generator, modulus);

    std::unordered_set<std::string> pairs;
    for (long d = 1; d <= p / 2; ++d) {
        GF2X invariant = NTL::PowerMod(1 + powers[d], p, modulus);
        if (NTL::IsOne(invariant) || !pairs.insert(field_key(invariant)).second)
            throw std::runtime_error("a three- or four-term relation survived");
    }

    std::vector<bool> seen(p);
    std::unordered_map<std::uint64_t, unsigned> triples;
    long directions = 0, min_weight = degree + 1;
    for (long d = 1; d < p; ++d) {
        if (seen[d]) continue;
        ++directions;
        long b = d, period = 0;
        do {
            seen[b] = seen[p-b] = true;
            b = 2*b % p;
            ++period;
        } while (b != d);
        if (period != degree) throw std::runtime_error("incorrect doubling period");
        // The negative direction gives the reciprocal polynomial and the same weight.
        GF2X minimal = NTL::MinPolyMod(powers[d], modulus);
        if (NTL::deg(minimal) != degree || !NTL::IsZero(NTL::CompMod(minimal, powers[d], modulus)))
            throw std::runtime_error("invalid subgroup minimal polynomial");
        min_weight = std::min(min_weight, NTL::weight(minimal));

        const GF2X pair_sum = 1 + powers[d];
        for (long e = 1; e < p; ++e) {
            if (e == d) continue;
            GF2X invariant = NTL::PowerMod(pair_sum + powers[e], p, modulus);
            if (NTL::IsZero(invariant) || NTL::IsOne(invariant) || pairs.count(field_key(invariant)))
                throw std::runtime_error("a triple sums to zero, a singleton or a pair");
            ++triples[signature(invariant)];
        }
    }
    if (2*degree*directions != p-1 || min_weight != expected_min_weight)
        throw std::runtime_error("subgroup factor census mismatch");
    for (const auto& entry : triples)
        if (entry.second != 3) throw std::runtime_error("distinct triple orbits share a signature");
    std::cout << p << ": " << pairs.size() << " pair classes, " << directions*(p-2)
              << " normalized triples, " << triples.size() << " triple orbits, minimum polynomial weight "
              << min_weight << '\n';
}

int main() {
    GF2X f;
    for (long e : {0, 2, 6, 15, 1229}) NTL::SetCoeff(f, e);
    if (!prime(degree) || !NTL::IterIrredTest(f)) throw std::runtime_error("invalid field model");
    const GF2XModulus modulus(f);
    const FrobeniusSignature signature(modulus);
    check_subgroup(36871, 605, modulus, signature);
    check_subgroup(46703, 579, modulus, signature);
}
