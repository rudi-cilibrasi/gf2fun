// Count irreducible candidates and test membership in the product of the maximal subfields.
#include <NTL/GF2XFactoring.h>
#include <iostream>
#include <numeric>
#include <stdexcept>

int main() {
    long n, p, q, count;
    if (!(std::cin >> n >> p >> q >> count) || p < 3 || q <= p || n % (p*q) || count < 0)
        throw std::runtime_error("invalid degree or candidate count");

    const NTL::ZZ a = NTL::power2_ZZ(n/p) - 1, b = NTL::power2_ZZ(n/q) - 1;
    const NTL::ZZ bound = (a / NTL::GCD(a, b)) * b;
    long irreducible = 0, split = 0;
    for (long i = 0; i < count; ++i) {
        long x, y, z;
        if (!(std::cin >> x >> y >> z) || !(0 < x && x < y && y < z && z < n)
                || std::gcd(std::gcd(x, y), std::gcd(z, n)) != 1)
            throw std::runtime_error("invalid normalized pentanomial support");
        NTL::GF2X f;
        for (long k : {0L, x, y, z, n}) NTL::SetCoeff(f, k);
        if (!NTL::IterIrredTest(f)) continue;
        ++irreducible;
        if (NTL::IsOne(NTL::PowerXMod(bound, NTL::GF2XModulus(f)))) {
            ++split;
            std::cerr << "Split in degree " << n << " with taps " << x << ' ' << y << ' ' << z << '\n';
        }
    }
    std::cin >> std::ws;
    if (!std::cin.eof()) throw std::runtime_error("unexpected candidates after final row");
    std::cout << count << ' ' << irreducible << ' ' << split << '\n';
}
