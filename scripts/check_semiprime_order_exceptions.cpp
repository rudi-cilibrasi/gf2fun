// List every sparse irreducible with no full-degree prime in its root order.
// The inputs are distinct odd primes p < q with q dividing 2^p-1.
// In --verify-bases mode, read rows of the form "degree prime interior_taps".
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <limits>
#include <sstream>
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

bool verify_base(const std::string& line) {
    std::istringstream fields(line);
    long n, q, tap;
    if (!(fields >> n >> q) || n < 2 || q < 3 || !is_prime(q)) return false;
    GF2X f;
    NTL::SetCoeff(f, 0);
    NTL::SetCoeff(f, n);
    long previous = 0, count = 0;
    while (fields >> tap) {
        if (tap <= previous || tap >= n || ++count > 3) return false;
        NTL::SetCoeff(f, tap);
        previous = tap;
    }
    if (!fields.eof() || (count != 1 && count != 3)) return false;
    const NTL::ZZ order = NTL::power2_ZZ(n)-1;
    return order % q == 0 && NTL::IterIrredTest(f) &&
        !NTL::IsOne(NTL::PowerXMod(order/q, NTL::GF2XModulus(f)));
}

int verify_bases() {
    std::vector<std::string> lines;
    std::string line;
    while (std::getline(std::cin, line)) lines.push_back(line);
    if (lines.empty()) throw std::invalid_argument("expected at least one base polynomial");
    long failures = 0;
    #pragma omp parallel for schedule(dynamic) reduction(+:failures)
    for (size_t i = 0; i < lines.size(); ++i) {
        if (!verify_base(lines[i])) {
            ++failures;
            #pragma omp critical
            std::cerr << "failed base: " << lines[i] << '\n';
        }
    }
    std::cout << lines.size() << " base checks, " << failures << " failures\n";
    return failures != 0;
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
        if (argc == 2 && std::string(argv[1]) == "--verify-bases") return verify_bases();
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
