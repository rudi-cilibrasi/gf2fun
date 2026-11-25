// Exclude the subfield product for 3p/2 < q <= 9p/4, q <= 10000, and verify every prime exception.
#include <NTL/GF2XFactoring.h>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr long bound = 10000;

std::vector<long> odd_primes() {
    std::vector<bool> composite(bound + 1);
    for (long p = 2; p*p <= bound; ++p) {
        if (composite[p]) continue;
        for (long j = p*p; j <= bound; j += p) composite[j] = true;
    }
    std::vector<long> primes;
    for (long p = 3; p <= bound; p += 2)
        if (!composite[p]) primes.push_back(p);
    return primes;
}

std::vector<long> possible_orders(long d, long lo, long hi) {
    std::vector<long> orders;
    const long step = 2*d;
    // Every prime divisor of a nontrivial degree-d component is 1 modulo 2d.
    for (long v = 1 + step*((lo-1 + step-1)/step); v <= hi; v += step)
        if (NTL::PowerMod(2L, d, v) == 1) orders.push_back(v);
    return orders;
}

long plane_degree(long order) {
    NTL::GF2X f, g;
    NTL::SetCoeff(f, order);
    NTL::SetCoeff(f, 0);
    // Lucas's theorem gives the nonconstant terms of (X+1)^order+1.
    for (long j = order; j; j = (j-1) & order) NTL::SetCoeff(g, j);
    return NTL::deg(NTL::GCD(f, g));
}

void verify_seeds(const char *path, const std::set<long> &exceptions) {
    std::ifstream input(path);
    std::string line;
    if (!std::getline(input, line) || line != "p,q,taps")
        throw std::runtime_error("expected the seed CSV with columns p,q,taps");
    std::set<long> checked;
    while (std::getline(input, line)) {
        std::replace(line.begin(), line.end(), ',', ' ');
        std::istringstream row(line);
        long p, q, i;
        if (!(row >> p >> q) || !exceptions.count(p) || q != 2*p+1 || !checked.insert(p).second)
            throw std::runtime_error("invalid or repeated exceptional prime pair");
        NTL::GF2X f;
        NTL::SetCoeff(f, p);
        NTL::SetCoeff(f, 0);
        long last = 0;
        while (row >> i) {
            if (i <= last || i >= p) throw std::runtime_error("invalid seed tap");
            NTL::SetCoeff(f, i);
            last = i;
        }
        if (!row.eof() || (NTL::weight(f) != 3 && NTL::weight(f) != 5) || !NTL::IterIrredTest(f))
            throw std::runtime_error("invalid sparse seed at degree " + std::to_string(p));
        const NTL::ZZ group = NTL::power2_ZZ(p)-1;
        if (group % q || NTL::IsOne(NTL::PowerXMod(group/q, NTL::GF2XModulus(f))))
            throw std::runtime_error("the seed misses the required prime power");
    }
    if (checked != exceptions) throw std::runtime_error("incomplete exception table");
}
}

int main(int argc, char **argv) {
    if (argc > 2) return 2;
    const auto primes = odd_primes();
    std::map<long, std::vector<long>> small;
    for (long p : primes) {
        auto orders = possible_orders(p, (3*p*p+3)/4, std::min(9*p*p/8, p*bound/2));
        if (!orders.empty()) small.emplace(p, std::move(orders));
    }
    std::set<long> planes, exceptions;
    long pairs = 0, extended = 0, matches = 0;
    for (long q : primes) {
        for (long p : primes) {
            if (p >= q) break;
            if (4*q > 9*p) continue;
            ++pairs;
            if (2*q > 3*p) ++extended;
            if (q == 2*p+1 && q % 8 == 7) exceptions.insert(p);
        }
        const auto other = possible_orders(q, (3*q*q+7)/8, 2*q*q/3);
        for (const auto &[p, orders] : small) {
            if (4*q > 9*p || 2*q <= 3*p) continue;
            for (long P : orders) {
                if (2*P > p*q) continue;
                for (long Q : other) {
                    if (Q > p*q) continue;
                    planes.insert(P);
                    ++matches;
                }
            }
        }
    }
    for (long P : planes) {
        const long d = plane_degree(P);
        std::cout << "P=" << P << ", gcd degree " << d << '\n';
        if (d != 0) throw std::runtime_error("a candidate plane needs further examination");
    }
    verify_seeds(argc == 2 ? argv[1] : "data/semiprime-gap-seeds.csv", exceptions);
    std::cout << pairs << " prime pairs in the full interval, " << extended << " in the extension.\n"
              << matches << " possible order tuples excluded by " << planes.size() << " polynomial gcds.\n"
              << exceptions.size() << " exceptional pairs have verified sparse lifts.\n";
}
