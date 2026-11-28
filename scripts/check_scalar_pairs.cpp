// Search the rank-two subfield for a degree-pq product root of a pentanomial.
// Arguments are the two distinct prime degrees p < q and the proposed
// order h of the degree-p component. Outputs counts for that one order.
#include "scalar_pair_polynomials.h"
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <array>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>

using NTL::GF2X;

namespace {
using scalar_pairs::trinomial;
using scalar_pairs::cyclotomic;

using Pair = std::array<long, 2>;

std::vector<Pair> exponent_choices(long r, long h, long n, bool singleton) {
    std::vector<Pair> result;
    for (long a = r; a <= n; a += h) {
        if (r == 0 && a != 0) continue;
        if (singleton) {
            if (r != n%h || a == n) result.push_back({a,a});
        } else {
            for (long b = a+h; b <= n; b += h)
                if (r != n%h || b == n) result.push_back({a,b});
        }
    }
    return result;
}

struct Counts {
    NTL::ZZ planes{0};
    NTL::ZZ supports{0};
    long max_gcd_degree = 0;
    NTL::ZZ large_gcds{0};
    NTL::ZZ splits{0};
};

void check_plane(long n, long q, long h, const std::array<long,3>& residues, Counts& counts) {
    ++counts.planes;
    for (int singleton = 0; singleton < 3; ++singleton) {
        const auto singles = exponent_choices(residues[singleton], h, n, true);
        const auto first = exponent_choices(residues[(singleton+1)%3], h, n, false);
        const auto second = exponent_choices(residues[(singleton+2)%3], h, n, false);
        for (const Pair& s : singles) {
            long c = s[0];
            std::vector<GF2X> trinomials;
            for (const Pair& b : second) trinomials.push_back(trinomial(b[0], b[1], c));
            for (const Pair& a : first) {
                GF2X t = trinomial(a[0], a[1], c);
                for (const GF2X& v : trinomials) {
                    ++counts.supports;
                    GF2X g = NTL::GCD(t, v);
                    counts.max_gcd_degree = std::max(counts.max_gcd_degree, NTL::deg(g));
                    if (NTL::deg(g) < q) continue;
                    ++counts.large_gcds;
                    NTL::GF2XModulus modulus(g);
                    GF2X x, y;
                    NTL::SetX(x);
                    y = x;
                    for (long j = 0; j < q; ++j) NTL::SqrMod(y, y, modulus);
                    if (!NTL::IsOne(NTL::GCD(g, y+x))) ++counts.splits;
                }
            }
        }
    }
}

int run(int argc, char** argv) {
    if (argc != 4) throw std::invalid_argument("expected p q h");
    long p = std::stol(argv[1]), q = std::stol(argv[2]), h = std::stol(argv[3]);
    if (p < 2 || q <= p || h < 3 || h%2 == 0 ||
        q > std::numeric_limits<long>::max()/p || h > p*q ||
        !NTL::ProbPrime(NTL::to_ZZ(p)) || !NTL::ProbPrime(NTL::to_ZZ(q)) ||
        NTL::PowerMod(NTL::to_ZZ(2), p, NTL::to_ZZ(h)) != 1)
        throw std::invalid_argument("invalid degrees or scalar order");
    long n = p*q, endpoint = n%h;
    GF2X phi = cyclotomic(h);
    Counts counts;
    // Residue zero occurs at the constant term. If the other endpoint
    // supplies a second residue, only the third remains to be chosen.
    for (long u = endpoint ? endpoint : 1; u < h; ++u) {
        for (long v = endpoint ? 1 : u+1; v < h; ++v) {
            if (u == v || NTL::IsOne(NTL::GCD(phi, trinomial(0,u,v)))) continue;
            check_plane(n, q, h, {0,u,v}, counts);
        }
        if (endpoint) break;
    }
    std::cout << counts.planes << ' ' << counts.supports << ' '
              << counts.max_gcd_degree << ' ' << counts.large_gcds << ' ' << counts.splits << '\n';
    return 0;
}
}

int main(int argc, char** argv) {
    try { return run(argc, argv); }
    catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
}
