// Exhaust the reciprocal classes of trinomials at each supplied degree.
// Input rows are: degree, number of order prime factors, then the primes
// with multiplicities. Verify primality of the factors with check_product_range.py.
// With --irreducible-only, each input row contains just a degree.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

bool passes_parity_test(long degree, long tap) {
    // Swan's parity conditions, with the square case and the middle tap handled directly.
    if (degree % 2 == 0) {
        if (tap % 2 == 0) return false;
        const long residue = ((degree / 2) % 4) * (tap % 4) % 4;
        return tap == degree / 2 || residue >= 2;
    }
    const long even_tap = tap % 2 == 0 ? tap : degree - tap;
    const bool divides_twice_degree = degree % (even_tap / 2) == 0;
    return divides_twice_degree == (degree % 8 == 3 || degree % 8 == 5);
}

int main(int argc, char** argv) {
    try {
        const bool irreducible_only = argc == 2 && std::string(argv[1]) == "--irreducible-only";
        if (argc != 1 && !irreducible_only)
            throw std::runtime_error("usage: prime_degree_trinomials [--irreducible-only]");
        std::cout << (irreducible_only ? "degree,irreducible_taps\n"
                                      : "degree,irreducible_taps,primitive_taps\n");
        long degree;
        while (std::cin >> degree) {
            if (degree < 2) throw std::runtime_error("invalid degree");
            NTL::ZZ order;
            std::vector<NTL::ZZ> factors;
            if (!irreducible_only) {
                long count;
                if (!(std::cin >> count) || count < 1 || count > degree)
                    throw std::runtime_error("invalid factor count");
                order = NTL::power2_ZZ(degree) - 1;
                NTL::ZZ product(1);
                factors.resize(count);
                for (auto& prime : factors) {
                    if (!(std::cin >> prime) || prime < 2)
                        throw std::runtime_error("invalid factor");
                    product *= prime;
                }
                if (product != order) throw std::runtime_error("incomplete factorization");
            }

            std::vector<long> irreducible, primitive;
            for (long tap = 1; tap <= degree / 2; ++tap) {
                if (!passes_parity_test(degree, tap)) continue;
                NTL::GF2X polynomial;
                for (long exponent : {0L, tap, degree}) NTL::SetCoeff(polynomial, exponent);
                if (!NTL::IterIrredTest(polynomial)) continue;
                irreducible.push_back(tap);
                if (irreducible_only) continue;
                NTL::GF2XModulus modulus(polynomial);
                bool full_order = true;
                for (const auto& prime : factors) {
                    if (NTL::IsOne(NTL::PowerXMod(order / prime, modulus))) {
                        full_order = false;
                        break;
                    }
                }
                if (full_order) primitive.push_back(tap);
            }
            std::cout << degree;
            auto print_taps = [](const std::vector<long>& taps) {
                std::cout << ',';
                for (std::size_t i = 0; i < taps.size(); ++i)
                    std::cout << (i == 0 ? "" : " ") << taps[i];
            };
            print_taps(irreducible);
            if (!irreducible_only) print_taps(primitive);
            std::cout << '\n';
        }
        if (!std::cin.eof()) throw std::runtime_error("invalid input row");
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
