// Exhaust the reciprocal classes of trinomials at each supplied degree.
// Input rows are: degree, number of order prime factors, then the primes
// with multiplicities. Verify primality of the factors with check_product_range.py.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

int main() {
    try {
        std::cout << "degree,irreducible_taps,primitive_taps\n";
        long degree;
        while (std::cin >> degree) {
            long count;
            if (degree < 2 || !(std::cin >> count) || count < 1 || count > degree)
                throw std::runtime_error("invalid degree or factor count");
            std::vector<NTL::ZZ> factors(count);
            NTL::ZZ order = NTL::power2_ZZ(degree) - 1;
            NTL::ZZ product(1);
            for (auto& prime : factors) {
                if (!(std::cin >> prime) || prime < 2)
                    throw std::runtime_error("invalid factor");
                product *= prime;
            }
            if (product != order) throw std::runtime_error("incomplete factorization");

            std::vector<long> irreducible, primitive;
            for (long tap = 1; tap <= degree / 2; ++tap) {
                NTL::GF2X polynomial;
                for (long exponent : {0L, tap, degree}) NTL::SetCoeff(polynomial, exponent);
                if (!NTL::IterIrredTest(polynomial)) continue;
                irreducible.push_back(tap);
                NTL::GF2XModulus modulus(polynomial);
                bool full_order = true;
                for (const auto& prime : factors)
                    if (NTL::IsOne(NTL::PowerXMod(order / prime, modulus)))
                        full_order = false;
                if (full_order) primitive.push_back(tap);
            }
            std::cout << degree;
            for (const auto* taps : {&irreducible, &primitive}) {
                std::cout << ',';
                for (std::size_t i = 0; i < taps->size(); ++i)
                    std::cout << (i == 0 ? "" : " ") << (*taps)[i];
            }
            std::cout << '\n';
        }
        if (!std::cin.eof()) throw std::runtime_error("invalid input row");
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
