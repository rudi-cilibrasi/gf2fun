// Weights of all binary irreducible factors of Phi_s for a prime s.
// Usage: cyclotomic_weight_census degree s interior_tap [interior_tap ...]
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
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

static void census(long n, long s, const GF2X& field) {
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
    std::vector<long> shift(2 * n);
    for (long j = 0; j < 2 * n; ++j)
        shift[j] = j % s ? coset.at(NTL::PowerMod(j % s, n, s)) : -1;
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

    // This identity independently certifies the entire list. Every root of Phi_s
    // has degree ord_s(2)=n, and Phi_s is squarefree.
    GF2X product = product_tree(std::move(polynomials));
    if (deg(product) != s - 1 || NTL::weight(product) != s)
        throw std::runtime_error("factor product is not Phi_s");
    // Phi_s(X+1) = ((X+1)^s+1)/X. Its exponents are the nonzero submasks of s minus one.
    GF2X expected_shift;
    for (long j = s; j > 0; j = (j - 1) & s) NTL::SetCoeff(expected_shift, j - 1);
    if (product_tree(std::move(translations)) != expected_shift)
        throw std::runtime_error("translated factor product is not Phi_s(X+1)");
    std::cout << "{\"degree\":" << n << ",\"prime\":" << s
              << ",\"additive_intersection\":" << additive_intersection << ",\"weights\":";
    print_histogram(weights);
    std::cout << ",\"translated_weights\":";
    print_histogram(translated_weights);
    std::cout << "}\n";
}

int main(int argc, char** argv) {
    try {
        if (argc < 4) throw std::invalid_argument("supply degree, prime and interior exponents");
        long n = std::stol(argv[1]), s = std::stol(argv[2]);
        if (n < 2 || n >= s || s >= NTL_SP_BOUND) throw std::invalid_argument("invalid degree or prime");
        GF2X field;
        NTL::SetCoeff(field, 0);
        NTL::SetCoeff(field, n);
        for (int i = 3; i < argc; ++i) {
            long a = std::stol(argv[i]);
            if (a <= 0 || a >= n || NTL::IsOne(NTL::coeff(field, a)))
                throw std::invalid_argument("invalid interior exponent");
            NTL::SetCoeff(field, a);
        }
        census(n, s, field);
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
