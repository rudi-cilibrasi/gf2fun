#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: subfield_trinomial_factors MAX_DEGREE [FACTOR_DEGREE ...]\n";
        return 2;
    }
    const long limit = std::stol(argv[1]);
    if (limit < 2) return 2;
    std::vector<bool> needed(limit + 1, false);
    for (int j = 2; j < argc; ++j) {
        const long d = std::stol(argv[j]);
        if (d < 1 || d > limit) return 2;
        needed[d] = true;
    }
    #pragma omp parallel for schedule(dynamic)
    for (long t = 2; t <= limit; ++t) {
        std::ostringstream rows;
        for (long s = 1; s <= t / 2; ++s) {
            if (s % 2 == 0 && t % 2 == 0) continue;
            NTL::GF2X trinomial;
            NTL::SetCoeff(trinomial, t);
            NTL::SetCoeff(trinomial, s);
            NTL::SetCoeff(trinomial, 0);
            NTL::vec_pair_GF2X_long factors;
            NTL::CanZass(factors, trinomial);
            for (const auto& term : factors) {
                const auto& factor = term.a;
                const long d = NTL::deg(factor);
                if (!needed[d]) continue;
                std::vector<unsigned char> buf(NTL::NumBytes(factor));
                NTL::BytesFromGF2X(buf.data(), factor, buf.size());
                rows << t << ' ' << s << ' ' << d << ' ' << NTL::ZZFromBytes(buf.data(), buf.size()) << '\n';
            }
        }
        #pragma omp critical
        std::cout << rows.str();
    }
    std::cout << "finished\n";
}
