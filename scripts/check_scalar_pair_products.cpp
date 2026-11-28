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
#include <numeric>
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

std::vector<long> maximal_subfields(long degree) {
    std::vector<long> result;
    long left = degree;
    for (long p = 2; p <= left/p; ++p) {
        if (left%p) continue;
        result.push_back(degree/p);
        do { left /= p; } while (left%p == 0);
    }
    if (left > 1) result.push_back(degree/left);
    return result;
}

struct DegreeFactors {
    long q;
    std::vector<long> steps;

    explicit DegreeFactors(long degree) : q(degree), steps(maximal_subfields(degree)) {
        // X and X+1 cannot divide an input trinomial, which is nonzero at both points.
        steps.erase(std::remove(steps.begin(),steps.end(),1),steps.end());
        std::sort(steps.begin(),steps.end());
    }

    GF2X operator()(const GF2X& f) const {
        if (NTL::deg(f) < q) return GF2X(1);
        NTL::GF2XModulus modulus(f);
        GF2X x,y;
        NTL::SetX(x);
        y = x;
        GF2X smaller(1);
        long done = 0;
        for (long step : steps) {
            while (done < step) { NTL::SqrMod(y,y,modulus); ++done; }
            GF2X in_subfield = NTL::GCD(f,y+x);
            smaller *= in_subfield / NTL::GCD(smaller,in_subfield);
        }
        for (; done < q; ++done) NTL::SqrMod(y,y,modulus);
        return NTL::GCD(f,y+x) / smaller;
    }
};

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

    void add(const Counts& other, long n, bool reflect) {
        const long multiplier = reflect ? 2 : 1;
        supports += multiplier*other.supports;
        max_interior_gcd = std::max(max_interior_gcd,other.max_interior_gcd);
        interior_degree_q += multiplier*other.interior_degree_q;
        endpoint_degree_q += multiplier*other.endpoint_degree_q;
        splits.insert(other.splits.begin(),other.splits.end());
        if (reflect) {
            for (const auto& support : other.splits) {
                Support reciprocal;
                for (size_t i = 0; i < support.size(); ++i)
                    reciprocal[i] = n-support[support.size()-1-i];
                splits.insert(reciprocal);
            }
        }
    }
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
GF2X endpoint_candidates(long c, long h, long n, const DegreeFactors& factors) {
    long anchor = n-c;
    GF2X candidates;
    NTL::set(candidates);
    for (long a = anchor%h; a <= n; a += h) {
        if (a == anchor) continue;
        GF2X roots = factors(odd_part(trinomial(c,a,anchor)));
        candidates *= roots / NTL::GCD(candidates,roots);
    }
    return candidates;
}

void check_singleton(long c, long third, long h, long n, const DegreeFactors& factors,
                     const GF2X& endpoint_roots, Counts& counts) {
    const long q = factors.q, endpoint = n%h;
    const long left = n/h, right = (n-endpoint)/h, free = (n-third)/h+1;
    if (endpoint == 0) {
        // Both endpoints exhaust one pair, leaving a free pair in the third residue.
        counts.supports += NTL::to_ZZ(free)*(free-1)/2;
        GF2X roots = factors(odd_part(trinomial(0,c,n)));
        counts.endpoint_degree_q += NTL::deg(roots)/q;
        record(roots,q,c,0,third,h,n,counts);
    } else if (c != 0 && c != n) {
        counts.supports += NTL::to_ZZ(left)*right;
        GF2X a = anchored_product(c,0,h,n,q), b = anchored_product(c,n,h,n,q);
        GF2X g = NTL::GCD(a,b);
        counts.max_interior_gcd = std::max(counts.max_interior_gcd, NTL::deg(g));
        GF2X roots = factors(g);
        if (!NTL::IsOne(roots)) {
            ++counts.interior_degree_q;
            record(roots,q,c,0,endpoint,h,n,counts);
        }
    } else {
        long anchor = n-c;
        counts.supports += NTL::to_ZZ(anchor ? right : left)*free*(free-1)/2;
        counts.endpoint_degree_q += NTL::deg(endpoint_roots)/q;
        record(endpoint_roots,q,c,anchor%h,third,h,n,counts);
    }
}

int run(int argc, char** argv) {
    if (argc != 4) throw std::invalid_argument("expected p q h");
    long p = std::stol(argv[1]), q = std::stol(argv[2]), h = std::stol(argv[3]);
    if (p < 2 || q <= p || q > std::numeric_limits<long>::max()/p ||
        h <= 1 || h > p*q || h%2 == 0 || std::gcd(p,q) != 1 ||
        NTL::PowerMod(NTL::to_ZZ(2),p,NTL::to_ZZ(h)) != 1)
        throw std::invalid_argument("expected coprime degrees p < q and a scalar order dividing 2^p-1");
    for (long d : maximal_subfields(p))
        if (NTL::PowerMod(NTL::to_ZZ(2),d,NTL::to_ZZ(h)) == 1)
            throw std::invalid_argument("the scalar order must have full degree p");
    long n = p*q, endpoint = n%h, planes = 0;
    GF2X phi = cyclotomic(h);
    std::vector<std::array<long,2>> tasks;
    for (long u = endpoint ? endpoint : 1; u < h; ++u) {
        for (long v = endpoint ? 1 : u+1; v < h; ++v) {
            if (v == u || NTL::IsOne(NTL::GCD(phi,trinomial(0,u,v)))) continue;
            ++planes;
            if (endpoint) {
                tasks.push_back({0,v});
                tasks.push_back({n,v});
                for (long c = v; c <= n; c += h) tasks.push_back({c,v});
            } else {
                for (long c = v; c <= n; c += h) tasks.push_back({c,u});
                for (long c = u; c <= n; c += h) tasks.push_back({c,v});
            }
        }
        if (endpoint) break;
    }
    const DegreeFactors factors(q);
    GF2X endpoint_roots(1);
    if (endpoint && !tasks.empty()) endpoint_roots = endpoint_candidates(0,h,n,factors);
    // Reflection exchanges the endpoints and sends the singleton from c to n-c.
    tasks.erase(std::remove_if(tasks.begin(),tasks.end(),[n](const auto& task) {
        return task[0] > n/2;
    }),tasks.end());
    Counts total;
    #pragma omp parallel
    {
        Counts local;
        #pragma omp for schedule(dynamic)
        for (size_t i = 0; i < tasks.size(); ++i) {
            long c = tasks[i][0];
            Counts one;
            check_singleton(c, tasks[i][1], h, n, factors, endpoint_roots, one);
            local.add(one,n,c < n-c);
        }
        #pragma omp critical
        total.add(local,n,false);
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
