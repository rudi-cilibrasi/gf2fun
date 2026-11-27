// Check every five-term support for a product of elements of degrees p and q.
// For a fixed singleton, collect each side's trinomials in one binary product.
// A common degree-q irreducible must divide the gcd of the two products.
#include "scalar_pair_polynomials.h"
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <array>
#include <iostream>
#include <limits>
#include <set>
#include <stdexcept>
#include <vector>

using NTL::GF2X;
using Support = std::array<long, 5>;

namespace {
using scalar_pairs::trinomial;
using scalar_pairs::cyclotomic;

// Removing Frobenius multiplicity preserves all the roots.
GF2X odd_part(GF2X f) {
    while (NTL::IsZero(NTL::diff(f))) {
        GF2X g;
        for (long i = 0; 2*i <= NTL::deg(f); ++i)
            if (NTL::IsOne(NTL::coeff(f, 2*i))) NTL::SetCoeff(g, i);
        f.swap(g);
    }
    return f;
}

GF2X anchored_product(long c, long anchor, long h, long n, long q) {
    std::vector<GF2X> level;
    for (long a = anchor%h; a <= n; a += h) {
        if (a == anchor) continue;
        GF2X term = odd_part(trinomial(c, a, anchor));
        if (NTL::deg(term) >= q) level.push_back(std::move(term));
    }
    if (level.empty()) return GF2X(1);
    while (level.size() > 1) {
        size_t next = 0;
        for (size_t j = 0; j < level.size(); j += 2) {
            GF2X f;
            if (j+1 < level.size()) NTL::mul(f, level[j], level[j+1]);
            else f.swap(level[j]);
            level[next++].swap(f);
        }
        level.resize(next);
    }
    return level[0];
}

// Every input factor has constant coefficient one and odd weight, so the
// linear factors of X^(2^q)+X cannot occur. The other factors have degree q.
GF2X degree_q_part(const GF2X& f, long q) {
    if (NTL::deg(f) < q) return GF2X(1);
    NTL::GF2XModulus modulus(f);
    GF2X x, y;
    NTL::SetX(x);
    y = x;
    for (long j = 0; j < q; ++j) NTL::SqrMod(y, y, modulus);
    return NTL::GCD(f, y+x);
}

using Pair = std::array<long, 2>;

// Subtracting the smallest exponent from a trinomial preserves its
// nonzero roots. Both endpoints are mandatory whenever their class occurs.
std::vector<Pair> matching_pairs(const GF2X& factor, long c, long residue, long h, long n) {
    std::vector<Pair> result;
    for (long a = residue; a <= n; a += h) {
        if (residue == 0 && a != 0) continue;
        for (long b = a+h; b <= n; b += h) {
            if (residue == n%h && b != n) continue;
            if (NTL::IsZero(trinomial(a,b,c) % factor)) result.push_back({a,b});
        }
    }
    return result;
}

struct Counts {
    NTL::ZZ supports{0};
    long max_interior_gcd = 0;
    long interior_degree_q = 0;
    long endpoint_degree_q = 0;
    std::set<Support> splits;
};

void record(const GF2X& roots, long q, long c, long r, long s, long h, long n,
            Counts& counts) {
    if (NTL::IsOne(roots)) return;
    NTL::vec_GF2X factors;
    if (NTL::deg(roots) == q) factors.append(roots);
    else NTL::EDF(factors, roots, q);
    for (const auto& f : factors) {
        auto first = matching_pairs(f,c,r,h,n), second = matching_pairs(f,c,s,h,n);
        for (const auto& a : first) for (const auto& b : second) {
            Support support{a[0],a[1],b[0],b[1],c};
            std::sort(support.begin(),support.end());
            counts.splits.insert(support);
        }
    }
}

// These anchored factors are shared by every possible third residue.
GF2X endpoint_candidates(long c, long h, long n, long q) {
    long anchor = n-c;
    GF2X candidates;
    NTL::set(candidates);
    for (long a = anchor%h; a <= n; a += h) {
        if (a == anchor) continue;
        GF2X roots = degree_q_part(odd_part(trinomial(c,a,anchor)),q);
        candidates *= roots / NTL::GCD(candidates,roots);
    }
    return candidates;
}

void check_singleton(long c, long third, long h, long n, long q,
                     const std::array<GF2X,2>& endpoint_roots, Counts& counts) {
    long endpoint = n%h;
    const long left = n/h, right = (n-endpoint)/h, free = (n-third)/h+1;
    if (c != 0 && c != n) {
        counts.supports += NTL::to_ZZ(left)*right;
        GF2X a = anchored_product(c,0,h,n,q), b = anchored_product(c,n,h,n,q);
        GF2X g = NTL::GCD(a,b);
        counts.max_interior_gcd = std::max(counts.max_interior_gcd, NTL::deg(g));
        GF2X roots = degree_q_part(g,q);
        if (!NTL::IsOne(roots)) {
            ++counts.interior_degree_q;
            record(roots,q,c,0,endpoint,h,n,counts);
        }
    } else {
        long anchor = n-c;
        counts.supports += NTL::to_ZZ(anchor ? right : left)*free*(free-1)/2;
        const GF2X& candidates = endpoint_roots[c == 0 ? 0 : 1];
        counts.endpoint_degree_q += NTL::deg(candidates)/q;
        record(candidates,q,c,anchor%h,third,h,n,counts);
    }
}

int run(int argc, char** argv) {
    if (argc != 4) throw std::invalid_argument("expected p q h");
    long p = std::stol(argv[1]), q = std::stol(argv[2]), h = std::stol(argv[3]);
    if (p < 2 || q <= p || q > std::numeric_limits<long>::max()/p ||
        h <= 1 || h > p*q || h%2 == 0 || p*q%h == 0 ||
        !NTL::ProbPrime(NTL::to_ZZ(p)) || !NTL::ProbPrime(NTL::to_ZZ(q)) ||
        NTL::PowerMod(NTL::to_ZZ(2),p,NTL::to_ZZ(h)) != 1)
        throw std::invalid_argument("expected distinct prime degrees and a scalar order with distinct endpoint residues");
    long n = p*q, endpoint = n%h, planes = 0;
    GF2X phi = cyclotomic(h);
    std::vector<std::array<long,2>> tasks;
    for (long v = 1; v < h; ++v) {
        if (v == endpoint || NTL::IsOne(NTL::GCD(phi,trinomial(0,endpoint,v)))) continue;
        ++planes;
        tasks.push_back({0,v});
        tasks.push_back({n,v});
        for (long c = v; c <= n; c += h) tasks.push_back({c,v});
    }
    const std::array<GF2X,2> endpoint_roots{endpoint_candidates(0,h,n,q), endpoint_candidates(n,h,n,q)};
    Counts total;
    #pragma omp parallel
    {
        Counts local;
        #pragma omp for schedule(dynamic)
        for (size_t i = 0; i < tasks.size(); ++i)
            check_singleton(tasks[i][0], tasks[i][1], h, n, q, endpoint_roots, local);
        #pragma omp critical
        {
            total.supports += local.supports;
            total.max_interior_gcd = std::max(total.max_interior_gcd,local.max_interior_gcd);
            total.interior_degree_q += local.interior_degree_q;
            total.endpoint_degree_q += local.endpoint_degree_q;
            total.splits.insert(local.splits.begin(),local.splits.end());
        }
    }
    std::cout << planes << ' ' << total.supports << ' ' << total.max_interior_gcd << ' '
              << total.interior_degree_q << ' ' << total.endpoint_degree_q << ' '
              << total.splits.size() << '\n';
    return 0;
}
}
int main(int argc,char**argv) {
    try { return run(argc,argv); }
    catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
}
