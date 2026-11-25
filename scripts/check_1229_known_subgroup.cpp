// Count degree-1229 pentanomials dividing X^K+1, up to reciprocal pairs.
#include "pentanomial_1229_supports.hpp"
#include <iostream>
#include <string>

using namespace pentanomial_1229;

int main(int argc, char **argv) {
    int first = 1, last = degree / 2;
    if (argc == 3) {
        first = std::stoi(argv[1]);
        last = std::stoi(argv[2]);
    }
    if ((argc != 1 && argc != 3) || first < 1 || last < first || last > degree / 2) {
        std::cerr << "usage: check_1229_known_subgroup [first_tap last_tap]\n";
        return 2;
    }
    const NTL::ZZ order = NTL::conv<NTL::ZZ>("9536289355314392579996071515160583098298616686033085857")
                        * NTL::conv<NTL::ZZ>("10543179280661916121033") * 36871 * 46703;
    const auto factors = small_factors();
    // Store shards in tap order even if several threads finish out of order.
    std::vector<Counts> results(last - first + 1);
    std::vector<long> divisors(last - first + 1);
    #pragma omp parallel for schedule(dynamic, 1)
    for (int a = first; a <= last; ++a) {
        results[a - first] = visit_tap(a, factors, [&](int b, int c) {
            NTL::GF2X f, power;
            for (int i : {0, a, b, c, degree}) NTL::SetCoeff(f, i);
            NTL::PowerXMod(power, order, NTL::GF2XModulus(f));
            if (NTL::IsOne(power)) {
                ++divisors[a - first];
                #pragma omp critical
                std::cerr << "divisor " << a << ' ' << b << ' ' << c << '\n';
            }
        });
    }
    std::cout << "smallest_tap,supports,power_tests,divisors\n";
    for (int a = first; a <= last; ++a) {
        const auto &row = results[a - first];
        std::cout << a << ',' << row.supports << ',' << row.tested << ',' << divisors[a - first] << '\n';
    }
}
