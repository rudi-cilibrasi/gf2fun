// Read the 176 primitive degree-11 binary seed masks and their trace exponents.
// Emit a matrix of minimal-polynomial weights, one row per source seed.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <atomic>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int seed_degree = 11;
constexpr int n = (1 << seed_degree) - 1;

NTL::GF2X lift(int seed) {
    NTL::GF2X result;
    for (int j = 0; j <= seed_degree; ++j) {
        if ((seed >> j) & 1) NTL::SetCoeff(result, (1 << j) - 1);
    }
    return result;
}

int reciprocal(int seed) {
    int result = 0;
    for (int j = 0; j <= seed_degree; ++j) result = 2*result + ((seed >> j) & 1);
    return result;
}
}

int main(int argc, char **argv) {
    if (argc != 2) throw std::invalid_argument("usage: census_2047_trace_powers THREADS");
    const int threads = std::stoi(argv[1]);
    if (threads < 1) throw std::invalid_argument("expected a positive thread count");
    const NTL::ZZ size = (NTL::ZZ(1) << n) - 1;
    std::vector<int> seeds;
    std::vector<NTL::GF2X> lifts;
    std::vector<NTL::ZZ> exponents;
    int seed;
    NTL::ZZ exponent;
    while (std::cin >> seed >> exponent) {
        if (seed <= n || seed > 2*n+1 || !(seed & 1) || (!seeds.empty() && seed <= seeds.back())
            || exponent <= 0 || exponent >= size || !NTL::IsOne(NTL::GCD(exponent, size)))
            throw std::runtime_error("invalid seed order, mask, or trace exponent");
        auto f = lift(seed);
        if (!NTL::IterIrredTest(f)) throw std::runtime_error("reducible source lift");
        seeds.push_back(seed);
        lifts.push_back(f);
        exponents.push_back(exponent);
    }
    const int count = static_cast<int>(seeds.size());
    if (!std::cin.eof() || count != 176) throw std::runtime_error("incomplete seed list");
    std::vector<std::vector<int>> weights(count, std::vector<int>(count));
    std::atomic<bool> failed(false);
    #pragma omp parallel for num_threads(threads) schedule(dynamic)
    for (int i = 0; i < count; ++i) {
        NTL::GF2XModulus field(lifts[i]);
        const NTL::GF2X diagonal = lift(reciprocal(seeds[i]));
        for (int j = 0; j < count; ++j) {
            auto root = NTL::PowerXMod(exponents[j], field);
            auto minimum = NTL::MinPolyMod(root, field);
            if (NTL::deg(minimum) != n || !NTL::IsZero(NTL::CompMod(minimum, root, field))
                || (i == j && minimum != diagonal)) {
                failed.store(true);
                break;
            }
            weights[i][j] = NTL::weight(minimum);
        }
    }
    if (failed.load()) throw std::runtime_error("minimal polynomial or reciprocal image failed");
    for (int i = 0; i < count; ++i) {
        std::cout << seeds[i];
        for (int weight : weights[i]) std::cout << ' ' << weight;
        std::cout << '\n';
    }
}
