// Census product pentanomials in odd degrees with a partially factored group order.
// Each input line is n, the cofactor, and the known prime factors (with multiplicity), space separated.
#include <NTL/GF2XFactoring.h>
#include <algorithm>
#include <iostream>
#include <limits>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>

namespace {
using namespace NTL;

struct Counts {
    long supports = 0, squarefree = 0, reciprocal_free = 0, opposite = 0, opposite_free = 0;
    std::vector<std::pair<long, long>> irreducibles;  // (larger tap, missing mask)
};

GF2X trace_polynomial(long slope, long gap) {
    GF2X trace;
    for (long i : {0L, 1L, gap-1, slope, (gap-slope) % gap})
        SetCoeff(trace, i, coeff(trace, i) + 1);
    return trace;
}

void census(long n, const ZZ &cofactor, std::vector<ZZ> primes, bool list) {
    if (n < 3 || n % 2 == 0 || n > std::numeric_limits<int>::max() / 2 || cofactor <= 1)
        throw std::invalid_argument("expected an odd degree and nontrivial cofactor");
    const ZZ group = power2_ZZ(n) - 1;
    ZZ known(1);
    for (const auto &p : primes) {
        if (p < 2 || !ProbPrime(p)) throw std::invalid_argument("invalid known prime");
        known *= p;
    }
    if (known * cofactor != group || !IsOne(GCD(known, cofactor)))
        throw std::invalid_argument("known factors and cofactor do not split the group order");
    std::sort(primes.begin(), primes.end());
    primes.erase(std::unique(primes.begin(), primes.end()), primes.end());
    if (primes.size()+1 >= std::numeric_limits<long>::digits)
        throw std::invalid_argument("too many distinct prime factors for the projection mask");
    std::vector<ZZ> powers;
    for (const auto &p : primes) powers.push_back(group / p);
    powers.push_back(known);

    std::vector<Counts> rows(n/2+1);
    #pragma omp parallel for schedule(dynamic, 1)
    for (long a = 1; a <= n/2; ++a) {
        auto &r = rows[a];
        for (long b = a+1; a+b < n; ++b) {
            ++r.supports;
            GF2X f, circle;
            for (long i : {0L, a, b, a+b, n}) SetCoeff(f, i);
            const long gap = 2*n-a-b;
            SetCoeff(circle, gap);
            SetCoeff(circle, 0);
            const auto common = GCD(f, reverse(f, n));
            if (common != GCD(f, circle)) throw std::runtime_error("reciprocal gcd disagreement");
            const bool free = IsOne(common), squarefree = IsOne(GCD(f, diff(f)));
            r.reciprocal_free += free;
            r.squarefree += squarefree;
            if ((a+b) % 2) {
                if (!squarefree) throw std::runtime_error("repeated root at opposite tap parities");
                ++r.opposite;
                r.opposite_free += free;
            }
            if (std::gcd(n, gap) == 1) {
                const long slope = SubMod(MulMod(a, InvMod(n, gap), gap), 1, gap);
                if (IsOne(GCD(trace_polynomial(slope, gap), circle)) != free)
                    throw std::runtime_error("cyclic trace disagreement");
            }
            if (!free || !squarefree || !IterIrredTest(f)) continue;
            const GF2XModulus modulus(f);
            long missing = 0;
            for (std::size_t i = 0; i < powers.size(); ++i) {
                GF2X value;
                PowerXMod(value, powers[i], modulus);
                if (IsOne(value)) missing |= 1L << i;
            }
            r.irreducibles.emplace_back(b, missing);
        }
    }
    Counts total;
    long irreducibles = 0, all = 0, inside = 0;
    for (long a = 1; a <= n/2; ++a) {
        const auto &r = rows[a];
        total.supports += r.supports;
        total.squarefree += r.squarefree;
        total.reciprocal_free += r.reciprocal_free;
        total.opposite += r.opposite;
        total.opposite_free += r.opposite_free;
        for (auto [b, missing] : r.irreducibles) {
            if (list) std::cout << n << ',' << a << ',' << b << ',' << missing << '\n';
            ++irreducibles;
            all += missing == 0;
            inside += (missing >> primes.size()) != 0;
        }
    }
    if (total.supports != (n/2)*((n-1)/2-1)) throw std::runtime_error("incomplete tap coverage");
    if (!list) std::cout << n << ',' << total.supports << ',' << total.squarefree << ','
        << total.reciprocal_free << ',' << total.opposite << ',' << total.opposite_free << ','
        << irreducibles << ',' << all << ',' << inside << '\n';
    std::cout.flush();
}
}

int main(int argc, char **argv) {
    try {
        const bool list = argc == 2 && std::string(argv[1]) == "--list";
        if (argc != 1 && !list) throw std::invalid_argument("usage: census_product_gaps [--list]");
        if (list) std::cout << "degree,u,v,missing_mask\n";
        else std::cout << "degree,supports,squarefree,reciprocal_free,opposite_taps,opposite_free,"
                          "irreducibles,all_projections,inside_known\n";
        std::string line;
        if (std::cin.peek() == std::char_traits<char>::eof())
            throw std::invalid_argument("expected at least one parameter row");
        while (std::getline(std::cin, line)) {
            std::istringstream stream(line);
            long n;
            NTL::ZZ cofactor, p;
            if (!(stream >> n >> cofactor)) throw std::invalid_argument("invalid parameter row");
            std::vector<NTL::ZZ> primes;
            while (stream >> p) primes.push_back(p);
            if (!stream.eof() || primes.empty()) throw std::invalid_argument("invalid prime list");
            census(n, cofactor, primes, list);
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
