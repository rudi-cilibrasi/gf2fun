// List every sparse irreducible with no full-degree prime in its root order.
// The inputs are distinct odd primes p < q with q dividing 2^p-1.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {
using NTL::GF2X;
using Taps = std::vector<long>;

bool is_prime(long n) {
    if (n < 2) return false;
    for (long i = 2; i <= n/i; ++i)
        if (n % i == 0) return false;
    return true;
}

long read_prime(const std::string& arg) {
    size_t end;
    const long value = std::stol(arg, &end);
    if (end != arg.size() || value < 3 || !is_prime(value))
        throw std::invalid_argument("expected an odd prime");
    return value;
}

struct Census {
    long singles = 0;
    long triples = 0;
    std::vector<Taps> exceptions;
};

void test(const GF2X& f, const NTL::ZZ& scalar_exponent, long q, Census& counts) {
    // A root passes exactly when X^(q*(2^p-1)) belongs to the degree-q subfield.
    const NTL::GF2XModulus modulus(f);
    GF2X y = NTL::PowerXMod(scalar_exponent, modulus), conjugate = y;
    for (long i = 0; i < q; ++i) NTL::SqrMod(conjugate, conjugate, modulus);
    if (conjugate != y || !NTL::IterIrredTest(f)) return;
    Taps taps;
    for (long j = 1; j < NTL::deg(f); ++j)
        if (NTL::IsOne(NTL::coeff(f, j))) taps.push_back(j);
    counts.exceptions.push_back(std::move(taps));
}

Census enumerate(long p, long q) {
    const long n = p*q;
    const NTL::ZZ exponent = q*(NTL::power2_ZZ(p)-1);
    std::vector<Census> rows(n/2+1);
    #pragma omp parallel for schedule(dynamic)
    for (long a = 1; a <= n/2; ++a) {
        Census& row = rows[a];
        GF2X f;
        NTL::SetCoeff(f, 0);
        NTL::SetCoeff(f, n);
        NTL::SetCoeff(f, a);
        ++row.singles;
        test(f, exponent, q, row);
        // Compare (a,b,c) lexicographically with (n-c,n-b,n-a).
        for (long b = a+1; b < n-a; ++b) {
            NTL::SetCoeff(f, b);
            const long last = b <= n/2 ? n-a : n-a-1;
            for (long c = b+1; c <= last; ++c) {
                NTL::SetCoeff(f, c);
                ++row.triples;
                test(f, exponent, q, row);
                NTL::SetCoeff(f, c, 0);
            }
            NTL::SetCoeff(f, b, 0);
        }
    }
    Census all;
    for (const auto& row : rows) {
        all.singles += row.singles;
        all.triples += row.triples;
        all.exceptions.insert(all.exceptions.end(), row.exceptions.begin(), row.exceptions.end());
    }
    return all;
}
} // namespace

int main(int argc, char** argv) {
    try {
        if (argc != 3) throw std::invalid_argument("usage: check_semiprime_order_exceptions p q");
        const long p = read_prime(argv[1]), q = read_prime(argv[2]);
        if (p >= q || p > std::numeric_limits<long>::max()/q || NTL::PowerMod(2L, p, q) != 1)
            throw std::invalid_argument("expected odd primes p < q with q dividing 2^p-1");
        const long n = p*q;
        const NTL::ZZ triples = NTL::to_ZZ(n-1)*(n-2)*(n-3)/12;
        if (triples > std::numeric_limits<long>::max())
            throw std::overflow_error("support count exceeds the counter size");
        const auto result = enumerate(p, q);
        if (result.singles != n/2 || result.triples != triples)
            throw std::runtime_error("incomplete reciprocal enumeration");
        std::cout << "degree " << n << ": " << result.singles << " trinomial pairs, "
                  << result.triples << " pentanomial pairs, " << result.exceptions.size()
                  << " exceptional reciprocal pair(s)\n";
        for (const auto& taps : result.exceptions) {
            std::cout << taps[0];
            for (size_t j = 1; j < taps.size(); ++j) std::cout << ' ' << taps[j];
            std::cout << '\n';
        }
    } catch (const std::exception& e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
