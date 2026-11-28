// Exhaust the reciprocal classes of trinomials at each supplied degree.
// Input rows are: degree, number of order prime factors, then the primes
// with multiplicities. Verify primality of the factors with check_product_range.py.
// With --irreducible-only, each input row contains just a degree.
// --sieve skips taps with a root in a smaller binary field of degree at most 21.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <numeric>
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

static std::vector<bool> small_factor_taps(long degree) {
    // A primitive polynomial per degree. Walking its full cycle below verifies each model.
    constexpr unsigned models[] = {0, 0, 0x7, 0xb, 0x13, 0x25, 0x43, 0x83, 0x11d,
        0x211, 0x409, 0x805, 0x1053, 0x201b, 0x402b, 0x8003, 0x1002d, 0x20009,
        0x40027, 0x80027, 0x100009, 0x200005};
    std::vector<bool> excluded(degree/2+1);
    for (int d = 2; d < degree && d <= 21; ++d) {
        const unsigned size = 1u << d, period = size-1;
        if (size/64 > static_cast<unsigned long>(degree)) break;
        std::vector<unsigned> powers(period), logs(size, period);
        unsigned value = 1;
        for (unsigned i = 0; i < period; ++i) {
            if (value == 0 || logs[value] != period)
                throw std::runtime_error("the small-field model has a short cycle");
            powers[i] = value;
            logs[value] = i;
            value <<= 1;
            if (value & size) value ^= models[d];
        }
        if (value != 1) throw std::runtime_error("the small-field cycle did not close");

        std::vector<bool> visited(period);
        for (unsigned h = 1; h < period; ++h) {
            if (visited[h]) continue;
            unsigned conjugate = h;
            do {
                visited[conjugate] = true;
                conjugate = 2*conjugate % period;
            } while (conjugate != h);
            // At x=a^h the equation is (a^h)^k = 1+(a^h)^degree.
            const auto exponent = std::uint64_t(h)*(degree % period) % period;
            const unsigned target = 1 ^ powers[exponent];
            if (target == 0) continue;
            const unsigned divisor = std::gcd(h, period);
            if (logs[target] % divisor) continue;
            const long modulus = period/divisor;
            const long first = NTL::MulMod(logs[target]/divisor,
                NTL::InvMod(h/divisor, modulus), modulus);
            for (long tap = first ? first : modulus; tap <= degree/2; tap += modulus)
                excluded[tap] = true;
        }
    }
    return excluded;
}

int main(int argc, char** argv) {
    try {
        bool irreducible_only = false, sieve = false;
        for (int i = 1; i < argc; ++i) {
            const std::string option(argv[i]);
            if (option == "--irreducible-only") irreducible_only = true;
            else if (option == "--sieve") sieve = true;
            else throw std::runtime_error("usage: prime_degree_trinomials [--irreducible-only] [--sieve]");
        }
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

            const auto excluded = sieve ? small_factor_taps(degree) : std::vector<bool>{};
            std::vector<long> irreducible, primitive;
#ifdef _OPENMP
            #pragma omp parallel for schedule(dynamic, 8) if(sieve)
#endif
            for (long tap = 1; tap <= degree / 2; ++tap) {
                if ((sieve && excluded[tap]) || !passes_parity_test(degree, tap)) continue;
                NTL::GF2X polynomial;
                for (long exponent : {0L, tap, degree}) NTL::SetCoeff(polynomial, exponent);
                if (!NTL::IterIrredTest(polynomial)) continue;
                bool full_order = false;
                if (!irreducible_only) {
                    NTL::GF2XModulus modulus(polynomial);
                    full_order = std::none_of(factors.begin(), factors.end(), [&](const NTL::ZZ& prime) {
                        return NTL::IsOne(NTL::PowerXMod(order / prime, modulus));
                    });
                }
#ifdef _OPENMP
                #pragma omp critical
#endif
                {
                    irreducible.push_back(tap);
                    if (full_order) primitive.push_back(tap);
                }
            }
            std::sort(irreducible.begin(), irreducible.end());
            std::sort(primitive.begin(), primitive.end());
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
