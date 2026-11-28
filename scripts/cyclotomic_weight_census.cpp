// Weights of all binary irreducible factors of Phi_s for a prime s.
// Usage: cyclotomic_weight_census [--prefix-bound | --check-factors] degree s interior_tap [...]
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using NTL::GF2X;

static std::vector<long> prime_factors(long value) {
    std::vector<long> factors;
    for (long p = 2; p <= value / p; ++p) {
        if (value % p != 0) continue;
        factors.push_back(p);
        do { value /= p; } while (value % p == 0);
    }
    if (value > 1) factors.push_back(value);
    return factors;
}

static bool has_order(long element, long order, long prime) {
    if (NTL::PowerMod(element, order, prime) != 1) return false;
    for (long p : prime_factors(order))
        if (NTL::PowerMod(element, order / p, prime) == 1) return false;
    return true;
}

static GF2X product_tree(std::vector<GF2X> level) {
    while (level.size() > 1) {
        std::vector<GF2X> next;
        for (size_t i = 0; i < level.size(); i += 2) {
            if (i + 1 == level.size()) next.push_back(std::move(level[i]));
            else next.push_back(level[i] * level[i + 1]);
        }
        level.swap(next);
    }
    return std::move(level.front());
}

static std::string encode(const GF2X& f, long bytes) {
    std::string result(bytes, '\0');
    NTL::BytesFromGF2X(reinterpret_cast<unsigned char*>(result.data()), f, bytes);
    return result;
}

// In the binary digits of an exponent, translation replaces each X^(2^j)
// by 1+X^(2^j). Add the upper half of each block of coefficients to its lower half.
static GF2X translate(const GF2X& f) {
    long length = 1;
    while (8 * length <= deg(f)) length *= 2;
    std::vector<unsigned char> bytes(length);
    NTL::BytesFromGF2X(bytes.data(), f, length);
    for (auto& b : bytes) {
        b ^= (b >> 1) & 0x55;
        b ^= (b >> 2) & 0x33;
        b ^= (b >> 4) & 0x0f;
    }
    for (long half = 1; half < length; half *= 2)
        for (long block = 0; block < length; block += 2 * half)
            for (long j = block; j < block + half; ++j) bytes[j] ^= bytes[j + half];
    return NTL::GF2XFromBytes(bytes.data(), length);
}

static void print_histogram(const std::map<long, long>& counts) {
    std::cout << '{';
    bool first = true;
    for (const auto& [weight, number] : counts) {
        if (!first) std::cout << ',';
        std::cout << '"' << weight << "\":" << number;
        first = false;
    }
    std::cout << '}';
}

// Bit j-1 represents Z^j in ZG'/G through degree 64 for G with the prescribed taps.
static std::uint64_t trace_prefix(const std::array<unsigned, 4>& taps, unsigned used) {
    std::uint64_t trace = 0;
    for (unsigned i = 0; i < used; ++i)
        if (taps[i] % 2) trace |= std::uint64_t(1) << (taps[i]-1);
    // If G=1+D, its inverse is the product of 1+D^(2^i) to this precision.
    for (unsigned power = 1; power < 64; power *= 2) {
        const auto previous = trace;
        for (unsigned i = 0; i < used && taps[i]*power < 64; ++i)
            trace ^= previous << (taps[i]*power);
    }
    return trace;
}

static void prefix_costs(std::unordered_map<std::uint64_t, unsigned>& cost,
                         std::array<unsigned, 4>& taps, unsigned used) {
    auto [position, inserted] = cost.emplace(trace_prefix(taps, used), used);
    if (!inserted) position->second = std::min(position->second, used);
    if (used == taps.size()) return;
    for (unsigned j = used ? taps[used-1]+1 : 1; j <= 64; ++j) {
        taps[used] = j;
        prefix_costs(cost, taps, used+1);
    }
}

static void prefix_bound(long n, long s, const std::vector<long>& trace,
                         const std::vector<long>& shift) {
    std::unordered_map<std::uint64_t, unsigned> cost;
    std::array<unsigned, 4> taps{};
    prefix_costs(cost, taps, 0);
    const long count = trace.size();
    std::vector<unsigned> ends(count);
    for (long i = 0; i < count; ++i) {
        std::uint64_t signature = 0;
        for (long j = 1; j <= 64; ++j)
            signature |= std::uint64_t(trace[(i + shift[j]) % count]) << (j-1);
        auto match = cost.find(signature);
        ends[i] = match == cost.end() ? taps.size()+1 : match->second;
    }
    unsigned minimum = 2 + 2*(taps.size()+1);
    for (long i = 0; i < count; ++i) {
        long reciprocal = n % 2 ? (i + count/2) % count : i;
        minimum = std::min(minimum, 2 + ends[i] + ends[reciprocal]);
    }
    // The two endpoints are disjoint, and every irreducible here has odd weight.
    if (minimum % 2 == 0) ++minimum;
    std::cout << "{\"degree\":" << n << ",\"prime\":" << s << ",\"factors\":" << count
              << ",\"minimum_weight_at_least\":" << minimum << "}\n";
}

static void check_factors(long s, const std::vector<GF2X>& polynomials,
                          const std::vector<GF2X>& translations) {
    GF2X shifted_x;
    NTL::SetCoeff(shifted_x, 0);
    NTL::SetCoeff(shifted_x, 1);
    std::vector<unsigned char> valid(polynomials.size());
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 16)
#endif
    for (long i = 0; i < static_cast<long>(polynomials.size()); ++i) {
        valid[i] = NTL::IsOne(NTL::PowerXMod(s, NTL::GF2XModulus(polynomials[i])))
                   && NTL::IsOne(NTL::PowerMod(shifted_x, s, NTL::GF2XModulus(translations[i])))
                   && translate(translations[i]) == polynomials[i];
    }
    if (std::find(valid.begin(), valid.end(), 0) != valid.end())
        throw std::runtime_error("a polynomial failed the cyclotomic divisibility or translation check");
}

static void census(long n, long s, const GF2X& field, bool prefix_only, bool individual) {
    if (n < 2 || s <= n || s >= NTL_SP_BOUND || prime_factors(s) != std::vector<long>{s}
            || (s - 1) % n || !has_order(2, n, s))
        throw std::invalid_argument("s must be a prime for which 2 has the specified degree");
    if (deg(field) != n || !NTL::IterIrredTest(field))
        throw std::invalid_argument("invalid binary field polynomial");
    NTL::GF2XModulus modulus(field);
    GF2X z = NTL::PowerXMod((NTL::power2_ZZ(n) - 1) / s, modulus);
    if (NTL::IsOne(z) || !NTL::IsOne(NTL::PowerMod(z, s, modulus)))
        throw std::invalid_argument("the supplied field generator did not project to order s");

    // Cosets of <2> are indexed by g^i. Raising a residue to n identifies its coset.
    long g = 2;
    while (!has_order(g, s - 1, s)) ++g;
    const long count = (s - 1) / n;
    const long unit = NTL::PowerMod(g, n, s);
    std::unordered_map<long, long> coset;
    std::vector<long> trace(count);
    long key = 1;
    for (long i = 0; i < count; ++i) {
        coset.emplace(key, i);
        trace[i] = NTL::rep(NTL::TraceMod(z, modulus));
        key = NTL::MulMod(key, unit, s);
        z = NTL::PowerMod(z, g, modulus);
    }

    // Tr(z^(g^i*j)) equals the period at i+coset(j). At j=0 it is n mod 2.
    const long length = prefix_only ? 65 : 2*n;
    std::vector<long> shift(length);
    for (long j = 0; j < length; ++j)
        shift[j] = j % s ? coset.at(NTL::PowerMod(j % s, n, s)) : -1;
    if (prefix_only) {
        prefix_bound(n, s, trace, shift);
        return;
    }
    std::vector<GF2X> polynomials;
    polynomials.reserve(count);
    NTL::vec_GF2 sequence;
    sequence.SetLength(2 * n);
    // For odd n, -1 represents the coset count/2 and gives reciprocal pairs.
    const long representatives = n % 2 ? count / 2 : count;
    for (long i = 0; i < representatives; ++i) {
        for (long j = 0; j < 2 * n; ++j)
            sequence[j] = shift[j] < 0 ? n % 2 : trace[(i + shift[j]) % count];
        GF2X f = NTL::MinPolySeq(sequence, n);
        if (deg(f) != n) throw std::runtime_error("trace recurrence has the wrong degree");
        if (n % 2) polynomials.push_back(NTL::reverse(f));
        polynomials.push_back(std::move(f));
    }

    const long bytes = n / 8 + 1;
    std::unordered_set<std::string> keys;
    for (const auto& f : polynomials) keys.insert(encode(f, bytes));
    if (keys.size() != polynomials.size()) throw std::runtime_error("repeated minimal polynomial");
    std::map<long, long> weights, translated_weights;
    std::vector<GF2X> translations;
    translations.reserve(count);
    long additive_intersection = 0;
    for (const auto& f : polynomials) {
        GF2X shifted = translate(f);
        ++weights[NTL::weight(f)];
        ++translated_weights[NTL::weight(shifted)];
        if (keys.count(encode(shifted, bytes))) additive_intersection += n;
        translations.push_back(std::move(shifted));
    }

    if (individual) {
        // Every nontrivial root has degree n. The (s-1)/n distinct monic divisors exhaust Phi_s.
        check_factors(s, polynomials, translations);
    } else {
        GF2X product = product_tree(std::move(polynomials));
        if (deg(product) != s - 1 || NTL::weight(product) != s)
            throw std::runtime_error("factor product is not Phi_s");
        // Phi_s(X+1) = ((X+1)^s+1)/X. Its exponents are the nonzero submasks of s minus one.
        GF2X expected_shift;
        for (long j = s; j > 0; j = (j - 1) & s) NTL::SetCoeff(expected_shift, j - 1);
        if (product_tree(std::move(translations)) != expected_shift)
            throw std::runtime_error("translated factor product is not Phi_s(X+1)");
    }
    std::cout << "{\"degree\":" << n << ",\"prime\":" << s
              << ",\"additive_intersection\":" << additive_intersection << ",\"weights\":";
    print_histogram(weights);
    std::cout << ",\"translated_weights\":";
    print_histogram(translated_weights);
    std::cout << "}\n";
}

int main(int argc, char** argv) {
    try {
        const std::string option = argc > 1 ? argv[1] : "";
        const bool prefix_only = option == "--prefix-bound";
        const bool individual = option == "--check-factors";
        const int first = prefix_only || individual ? 2 : 1;
        if (argc < first+3) throw std::invalid_argument("supply degree, prime and interior exponents");
        long n = std::stol(argv[first]), s = std::stol(argv[first+1]);
        if (n < 2 || n >= s || s >= NTL_SP_BOUND) throw std::invalid_argument("invalid degree or prime");
        if (prefix_only && n <= 128) throw std::invalid_argument("disjoint 64-bit ends require degree above 128");
        GF2X field;
        NTL::SetCoeff(field, 0);
        NTL::SetCoeff(field, n);
        for (int i = first+2; i < argc; ++i) {
            long a = std::stol(argv[i]);
            if (a <= 0 || a >= n || NTL::IsOne(NTL::coeff(field, a)))
                throw std::invalid_argument("invalid interior exponent");
            NTL::SetCoeff(field, a);
        }
        census(n, s, field, prefix_only, individual);
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
